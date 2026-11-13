module

public import Silmaril.Proofs.Wasm.Logic.Iris.Heap
public import Silmaril.Proofs.Wasm.Logic.Iris.Lifting
public import Iris.ProgramLogic.Adequacy
public import Silmaril.Wasm.Logic.Iris.Adequacy.Defs

/-!
# The Iris logic of Wasm Core 3.0: adequacy

`hwp_of_adequate` turns Iris's `adequate` (no reachable thread is stuck, and
every finished thread satisfies the postcondition) for `IExpr P host` into
Silmaril's every-run weakest precondition `Silmaril.Wasm.Logic.Hoare.HWP`:
every Core 3.0 configuration reachable by `Step P host` is safe. `wp_hwp` is
the adequacy theorem: a weakest precondition proved from the ownership of
cells that the store holds gives `HWP`.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.IrisWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare (Exits Safe HWP)
open _root_.Iris _root_.Iris.BI _root_.Iris.Std _root_.Iris.ProgramLogic
open _root_.Iris.ProgramLogic.Language.Notation

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Runs of the language -/

theorem primStep_of_step {s s' : Store H} {f f' : Frame} {c c' : List Admin}
    (h : Step P host ⟨s, f, c⟩ ⟨s', f', c'⟩) :
    ((IExpr.run c : IExpr P host), ((s, f) : IState H)) -<([] : List Empty)>->
      (IExpr.run c', ((s', f') : IState H), []) :=
  ⟨rfl, rfl, .step h⟩

theorem primStep_of_exits {s : Store H} {f : Frame} {c : List Admin} {o : Outcome}
    (h : Exits o c) :
    ((IExpr.run c : IExpr P host), ((s, f) : IState H)) -<([] : List Empty)>->
      (IExpr.done ⟨s, f, o⟩, ((s, f) : IState H), []) :=
  ⟨rfl, rfl, .exit h⟩

theorem erasedStep_of_step {s s' : Store H} {f f' : Frame} {c c' : List Admin}
    (h : Step P host ⟨s, f, c⟩ ⟨s', f', c'⟩) :
    Language.ErasedStep ([(IExpr.run c : IExpr P host)], ((s, f) : IState H))
      ([IExpr.run c'], (s', f')) :=
  ⟨[], Language.Step.atomic (primStep_of_step h) [] []⟩

theorem erasedStep_of_exits {s : Store H} {f : Frame} {c : List Admin} {o : Outcome}
    (h : Exits o c) :
    Language.ErasedStep ([(IExpr.run c : IExpr P host)], ((s, f) : IState H))
      ([IExpr.done ⟨s, f, o⟩], (s, f)) :=
  ⟨[], Language.Step.atomic (primStep_of_exits h) [] []⟩

/-- Every Core 3.0 run is a run of the language. -/
theorem reach_of_steps {s : Store H} {f : Frame} {c : List Admin} :
    ∀ {c' : Config H}, Steps P host ⟨s, f, c⟩ c' →
      ([(IExpr.run c : IExpr P host)], ((s, f) : IState H)) -·->ₜₚ*
        ([IExpr.run c'.code], (c'.store, c'.frame))
  | _, .refl => .refl
  | _, .tail hs h => .tail (reach_of_steps hs) (erasedStep_of_step h)

/-- **Iris adequacy gives every-run safety.** -/
theorem safe_of_adequate {s : Store H} {f : Frame} {code : List Admin} {Q : Post H}
    (had : adequate .NotStuck (IExpr.run code : IExpr P host) ((s, f) : IState H)
      (fun r _ => Q r.store r.frame r.out)) :
    ∀ (n : Nat) (c : Config H), Steps P host ⟨s, f, code⟩ c → Safe P host Q n c
  | 0, _, _ => trivial
  | n + 1, c, hs => by
    have hr := reach_of_steps hs
    by_cases hx : ∃ o, Exits o c.code
    · obtain ⟨o, he⟩ := hx
      have hq : Q c.store c.frame o :=
        had.adequate_result [] (c.store, c.frame) ⟨c.store, c.frame, o⟩ (hr.tail (erasedStep_of_exits he))
      exact .inl ⟨o, he, hq⟩
    · have hns : PrimStep.NotStuck ((IExpr.run c.code : IExpr P host), (c.store, c.frame)) :=
        had.adequate_not_stuck _ _ _ rfl hr (List.mem_singleton_self _)
      refine .inr ⟨?_, fun c' h => safe_of_adequate had n c' (hs.tail h)⟩
      rcases hns with hv | ⟨obs, e', σ', eₜ, -, -, hst⟩
      · cases hv
      · cases hst with
        | step h => exact ⟨_, h⟩
        | exit he => exact (hx ⟨_, he⟩).elim

theorem hwp_of_adequate {s : Store H} {f : Frame} {code : List Admin} {Q : Post H}
    (had : adequate .NotStuck (IExpr.run code : IExpr P host) ((s, f) : IState H)
      (fun r _ => Q r.store r.frame r.out)) : HWP P host s f code Q :=
  fun n => safe_of_adequate had n _ .refl

/-! ## Adequacy -/

variable {GF : BundledGFunctors}

local bi (IProp GF)

/-- The initial ghost heap: the cells `ps`. -/
theorem sub_updMap_empty {s : Store H} {f : Frame} {ps : List (ILoc × ICell)}
    (hnd : (ps.map Prod.fst).Nodup) (hps : ∀ p ∈ ps, cellOf s f p.1 = some p.2) :
    Sub (updMap ∅ ps) s f := by
  intro l c hl
  have hl' : (ps.lookup l).or (get? (∅ : HeapF ICell) l) = some c := by
    rw [← get?_updMap hnd]; exact hl
  have hc : ps.lookup l = some c := by simpa [get?_empty] using hl'
  exact hps _ (lookup_mem hc)

/-- **Adequacy.** If, for every allocation of the ghost names, the ownership of the
cells `ps` (which the store and frame hold) gives a weakest precondition with a
pure postcondition `Q`, then every run of the code from `s, f` is safe and every
exit satisfies `Q`. -/
theorem wp_hwp [WasmGpreS GF] {s : Store H} {f : Frame} {code : List Admin} {Q : Post H}
    (ps : List (ILoc × ICell)) (hnd : (ps.map Prod.fst).Nodup)
    (hps : ∀ p ∈ ps, cellOf s f p.1 = some p.2)
    (hwp : ∀ [WasmGS GF], ⊢ ownCells ps -∗
      WP (IExpr.run code : IExpr P host) {{ r, ⌜Q r.store r.frame r.out⌝ }}) :
    HWP P host s f code Q := by
  refine hwp_of_adequate (wp_adequacy (GF := GF) .NotStuck (IExpr.run code) (s, f)
    (fun r => Q r.store r.frame r.out) ?_)
  intro inst κs
  imod genHeap_init (GF := GF) (H := HeapF) (∅ : HeapF ICell) with ⟨%G, Hh, -⟩
  let instW : WasmGS GF := ⟨G⟩
  have hfr : ∀ q ∈ ps, get? (∅ : HeapF ICell) q.1 = none := fun _ _ => get?_empty _
  imod genHeap_alloc_cells hnd hfr $$ Hh with ⟨Hh, Hs⟩
  imodintro
  iexists (fun σ _ => wasmInterp σ), (fun _ => iprop(True))
  ihave Hwp := (@hwp instW) $$ Hs
  isplitr [Hwp]
  · unfold wasmInterp
    iexists updMap ∅ ps
    iframe
    ipureintro
    exact sub_updMap_empty hnd hps
  · iexact Hwp

/-- **An Iris triple gives the Silmaril triple**: every run from a state satisfying the
precondition is safe, and every exit satisfies the postcondition. -/
theorem ITriple.sound [WasmGpreS GF] {Pre : Store H → Frame → Prop}
    {own : Store H → Frame → List (ILoc × ICell)} {code : List Admin} {Q : Post H}
    (h : ITriple GF P host Pre own code Q) : Hoare.Triple P host Pre code Q := fun s f hp =>
  wp_hwp (own s f) (h s f hp).1 (h s f hp).2.1 (h s f hp).2.2

/-- **Iris adequacy, for every run**: a run of the code that ends in values `vs`
satisfies the postcondition at `normal vs`. -/
theorem wp_sound_vals [WasmGpreS GF] {s s' : Store H} {f f' : Frame} {code : List Admin}
    {Q : Post H} {vs : List Val} (ps : List (ILoc × ICell)) (hnd : (ps.map Prod.fst).Nodup)
    (hps : Cells ps s f)
    (hwp : ∀ [WasmGS GF], ⊢ ownCells ps -∗
      WP (IExpr.run code : IExpr P host) {{ r, ⌜Q r.store r.frame r.out⌝ }})
    (hs : Steps P host ⟨s, f, code⟩ ⟨s', f', vals vs⟩) : Q s' f' (.normal vs) :=
  (wp_hwp ps hnd hps hwp).sound_vals hs

/-- **Iris adequacy, safety**: every reachable configuration can step or has exited
with an outcome satisfying the postcondition. -/
theorem wp_sound [WasmGpreS GF] {s : Store H} {f : Frame} {code : List Admin} {Q : Post H}
    {c' : Config H} (ps : List (ILoc × ICell)) (hnd : (ps.map Prod.fst).Nodup)
    (hps : Cells ps s f)
    (hwp : ∀ [WasmGS GF], ⊢ ownCells ps -∗
      WP (IExpr.run code : IExpr P host) {{ r, ⌜Q r.store r.frame r.out⌝ }})
    (hs : Steps P host ⟨s, f, code⟩ c') :
    (∃ c'', Step P host c' c'') ∨ ∃ o, Exits o c'.code ∧ Q c'.store c'.frame o :=
  Hoare.hwp_sound (wp_hwp ps hnd hps hwp) hs

end Silmaril.Wasm.Logic.IrisWasm
