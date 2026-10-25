module

public import Silmaril.Wasm.SingleThreaded.Exec.RunInv
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateInit
public import Silmaril.Wasm.Execution.Core.Soundness

@[expose] public section

/-! # End-to-end: concrete instantiation followed by the run loop

`runModule? head n s m xas` instantiates `m` concretely (`instantiateInit?`) and
then runs the resulting configuration with the fuel-bounded driver `run? head n`.
Everything is parametric over the head function `head` and the deep head
invariant `Inv`.

* `instantiateInit?_ok`: the instantiated configuration is typed (`ConfigOk c []`)
  and reachable from an `Instantiate` configuration.
* `runModule?_sound`: the final configuration is reachable from an
  `Instantiate` configuration and typed; a classified outcome is the code.
* `runModule?_stopped`: a stopped result is terminal or can take a (necessarily
  host) step.
* `runModule?_complete`: a host-free normal form reachable from the
  instantiated configuration is found by the loop with enough fuel.
-/

namespace Silmaril.Wasm.SingleThreaded.Exec.EndToEnd

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.SingleThreaded.Exec
  Silmaril.Wasm.SingleThreaded.Exec.RunInv

variable {H : Type}

/-- Host-free step sequences are step sequences for any host. -/
theorem Steps.of_noHost {P : Profile} (host : HostSemantics H) {c c' : Config H}
    (h : Steps P (noHost (H := H)) c c') : Steps P host c c' := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact .tail ih (Step.of_noHost host hst)

/-- **(1)** The concretely instantiated configuration is typed and reachable
from an `Instantiate` configuration. -/
theorem instantiateInit?_ok {o : GrowOracle} {s : Store H} {m : Module}
    {xas : List ExternAddr} {c : Config H} (hs : StoreOk s)
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI)
    (h : instantiateInit? s m xas = some c) :
    ConfigOk c [] ∧ ∃ c₀, Instantiate (profile o) divHost s m xas c₀ ∧
      Steps (profile o) divHost c₀ c := by
  obtain ⟨c₀, hI, hst⟩ :=
    instantiateInit?_sound (P := profile o) (host := divHost) hvalid h
  have hc₀ : ConfigOk c₀ [] := Instantiate.ok divHost_ok hs hI
  exact ⟨(Steps.safe divHost_ok hc₀ hst).1, c₀, hI, hst⟩

/-- **(2)** Instantiate, then run: the final configuration, the stop flag, and
the classified outcome. -/
def runModule? (head : Store H → Frame → List Val → Admin → Option (Nat × Config H))
    (n : Nat) (s : Store H) (m : Module) (xas : List ExternAddr) :
    Option (Config H × Bool × Option Result) :=
  match instantiateInit? s m xas with
  | none => none
  | some c =>
    let r := run? head n c
    some (r.1, r.2, r.1.outcome?)

theorem runModule?_eq_some {head : Store H → Frame → List Val → Admin → Option (Nat × Config H)}
    {n : Nat} {s : Store H} {m : Module} {xas : List ExternAddr} {c' : Config H} {b : Bool}
    {r : Option Result} (h : runModule? head n s m xas = some (c', b, r)) :
    ∃ c, instantiateInit? s m xas = some c ∧ run? head n c = (c', b) ∧ r = c'.outcome? := by
  unfold runModule? at h
  split at h
  · cases h
  · rename_i c hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨c, hc, by rw [← h1, ← h2], by rw [← h3, h1]⟩

section run
variable {o : GrowOracle} {head : Store H → Frame → List Val → Admin → Option (Nat × Config H)}
  {Inv : Frame → Admin → Prop}

/-- **(3)** Soundness of `runModule?`. -/
theorem runModule?_sound
    (hInv : ∀ (c : Config H) ts, ConfigOk c ts → DeepAll Inv c.frame c.code)
    (hhead : HeadSoundAt o StoreOk Inv head)
    {n : Nat} {s : Store H} {m : Module} {xas : List ExternAddr} (hs : StoreOk s)
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI)
    {c' : Config H} {b : Bool} {r : Option Result}
    (h : runModule? head n s m xas = some (c', b, r)) :
    (∃ c₀, Instantiate (profile o) divHost s m xas c₀ ∧ Steps (profile o) divHost c₀ c') ∧
      ConfigOk c' [] ∧ (∀ res, r = some res → c'.code = res.toAdmin) := by
  obtain ⟨c, hc, hrun, rfl⟩ := runModule?_eq_some h
  obtain ⟨hok, c₀, hI, hst⟩ := instantiateInit?_ok (o := o) hs hvalid hc
  obtain ⟨hst', hok'⟩ := run?_steps_typed hInv hhead n hok hrun
  refine ⟨⟨c₀, hI, hst.trans (Steps.of_noHost divHost hst')⟩, hok', ?_⟩
  intro res hr
  exact Config.outcome?_sound hr

/-- The host-free part of soundness: the run is a host-free step sequence from
the instantiated configuration. -/
theorem runModule?_steps_noHost
    (hInv : ∀ (c : Config H) ts, ConfigOk c ts → DeepAll Inv c.frame c.code)
    (hhead : HeadSoundAt o StoreOk Inv head)
    {n : Nat} {s : Store H} {m : Module} {xas : List ExternAddr} (hs : StoreOk s)
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI)
    {c' : Config H} {b : Bool} {r : Option Result}
    (h : runModule? head n s m xas = some (c', b, r)) :
    ∃ c, instantiateInit? s m xas = some c ∧ Steps (profile o) noHost c c' := by
  obtain ⟨c, hc, hrun, rfl⟩ := runModule?_eq_some h
  obtain ⟨hok, -⟩ := instantiateInit?_ok (o := o) hs hvalid hc
  exact ⟨c, hc, (run?_steps_typed hInv hhead n hok hrun).1⟩

/-- **(4)** A stopped result is terminal or can only step through the host
(it has no host-free step). -/
theorem runModule?_stopped
    (hInv : ∀ (c : Config H) ts, ConfigOk c ts → DeepAll Inv c.frame c.code)
    (hhead : HeadSoundAt o StoreOk Inv head) (hx : HeadExactAt o StoreOk Inv head)
    {n : Nat} {s : Store H} {m : Module} {xas : List ExternAddr} (hs : StoreOk s)
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI)
    {c' : Config H} {r : Option Result}
    (h : runModule? head n s m xas = some (c', true, r)) :
    (c'.Terminal ∨ ∃ c'', Step (profile o) divHost c' c'') ∧
      ∀ c'', ¬ Step (profile o) noHost c' c'' := by
  obtain ⟨c, hc, hrun, rfl⟩ := runModule?_eq_some h
  obtain ⟨hok, -⟩ := instantiateInit?_ok (o := o) hs hvalid hc
  have hok' := (run?_steps_typed hInv hhead n hok hrun).2
  refine ⟨Config.progress divHost_ok hok', fun c'' hst => ?_⟩
  have := run?_stopped_no_step_typed hInv hhead hx (n := n) hok (by rw [hrun]) c''
  rw [hrun] at this
  exact this hst

/-- **(5)** Completeness: a host-free normal form reachable from the instantiated
configuration is found by `runModule?` with enough fuel. -/
theorem runModule?_complete
    (hInv : ∀ (c : Config H) ts, ConfigOk c ts → DeepAll Inv c.frame c.code)
    (hhead : HeadSoundAt o StoreOk Inv head) (hx : HeadExactAt o StoreOk Inv head)
    {s : Store H} {m : Module} {xas : List ExternAddr} (hs : StoreOk s)
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI)
    {c c' : Config H} (hc : instantiateInit? s m xas = some c)
    (h : Steps (profile o) noHost c c') (hnf : ∀ x, ¬ Step (profile o) noHost c' x) :
    ∃ n, runModule? head n s m xas = some (c', true, c'.outcome?) := by
  obtain ⟨hok, -⟩ := instantiateInit?_ok (o := o) hs hvalid hc
  obtain ⟨n, hn⟩ := run?_complete_typed hInv hhead hx hok h hnf
  refine ⟨n, ?_⟩
  unfold runModule?
  rw [hc]
  simp [hn]

end run

end Silmaril.Wasm.SingleThreaded.Exec.EndToEnd
