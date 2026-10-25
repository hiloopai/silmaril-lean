module

public import Silmaril.Wasm.Binaryen.InlAssemble
public import Silmaril.Wasm.SingleThreaded.Locality

@[expose] public section

/-! # Chosen original executions through the actual inlining relation

The main inliner's one-way simulation already preserves every chosen numerical
and growth outcome. This file supplies arbitrary-profile reachability and session
clients for that simulation. It does not derive reverse matching from unique
results or from termination excluding divergence: those deterministic arguments
in `InlAssemble.runs_corr` still need a separate chosen-run reverse simulation.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Validation Numerics SingleThreaded

variable {H : Type} {p : Prm} {P : Profile}

/-- An actual host-free reduction preserves the function table at every profile,
including nondeterministic numerical and memory-growth policies. -/
theorem noHost_funcs_profile {c c' : Config H} (h : Step P Det.noHost c c') :
    c'.store.funcs = c.store.funcs :=
  noHost_funcs h

/-- Every chosen typed execution stays classified and retains the function table.
No uniqueness or deterministic-profile property is needed. -/
theorem reach_classif_profile {host : HostSemantics H}
    (hR : HostRespectsCode host) (hok : HostOk host)
    {c : Config H} {ts : List CValType} (hc : ConfigOk c ts) {aw : Nat} {fw : FuncInst H}
    {cw : Func} (hfw : c.store.funcs[aw]? = some fw) (hcw : fw.code = .wasm cw) :
    ∀ x, Steps P host c x → Classif P host x ∧ x.store.funcs = c.store.funcs :=
  reach_classif hR hok hc hfw hcw

/-- Each terminating original execution has an inlined execution with exactly
the same values, trap or exception and the actual corresponding final store;
each diverging original execution has an inlined infinite execution. -/
theorem runs_forward_profile (hG : Good p) {host : HostSemantics H}
    (hR : HostRespectsCode host) (hok : HostOk host)
    {c c' : Config H} {ts : List CValType} (hc : ConfigOk c ts)
    (hMR : MR p .gen c c') (hSR : SR p c.store c'.store) :
    (∀ x, Steps P host c x → x.Terminal →
      ∃ x', Steps P host c' x' ∧ x'.code = x.code ∧ SR p x.store x'.store) ∧
    (Diverges P host c → Diverges P host c') := by
  obtain ⟨hpok, ⟨hC⟩, hfx⟩ := hG
  have hcl : ∀ x, Steps P host c x → Classif P host x :=
    fun x hx => (reach_classif_profile hR hok hc hSR.hg rfl x hx).1
  constructor
  · intro x hx ⟨r, hr⟩
    obtain ⟨x', hx', related, stores⟩ := run_sim hpok hfx hC hx hcl hMR hSR
    exact ⟨x', hx', by rw [terminal_code related hr, hr], stores⟩
  · intro diverges
    exact div_sim hpok hfx hC hR diverges hcl hMR hSR

/-- Persistent sessions of the original instance are reproduced by the inlined
store at the same arbitrary profile. Requests and all chosen results are retained;
the store relation is recovered after each completed call. -/
theorem session_forward_profile (hG : Good p) {host : HostSemantics H}
    (hR : HostRespectsCode host) (hok : HostOk host)
    {mi : ModuleInst} {s : Store H} {script : List Call} {bs : List (Behaviour Val)}
    (h : Session P host mi s script bs) :
    ∀ {t : Store H}, StoreOk s → StoreOk t → SR p s t → Session P host mi t script bs := by
  induction h with
  | nil => exact fun _ _ _ => .nil
  | stop h => exact fun _ _ hSR => .stop fun a ha hok' => h a ha (invokeOk_of' hSR hok')
  | @done s x vs rest a c r bs ha hok' run hr tail ih =>
    intro t hs ht hSR
    have hokN := invokeOk_of hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hok'
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hokN
    obtain ⟨forward, _⟩ := runs_forward_profile hG hR hok hcO (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    obtain ⟨x', hx', hcode, hSR'⟩ := forward c run ⟨r, hr⟩
    exact .done ha hokN hx' (by rw [hcode, hr])
      (ih (ConfigOk.storeOk (Steps.safe hok hcO run).1)
        (ConfigOk.storeOk (Steps.safe hok hcN hx').1) hSR')
  | @diverge s x vs rest a ha hok' hd =>
    intro t hs _ hSR
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hok'
    obtain ⟨_, diverges⟩ := runs_forward_profile hG hR hok hcO (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    exact .diverge ha (invokeOk_of hSR hok') (diverges hd)

end Silmaril.Wasm.Binaryen.InlR
