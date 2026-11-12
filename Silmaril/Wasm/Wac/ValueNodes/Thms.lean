module

public import Silmaril.Wasm.Wac.ValueNodes.Defs

/-!
# WAC: a composition with a value import or export has no composition graph

* `forM_error`: a `forM` in `StateT σ (Except ε)` fails when one of its steps fails from every
  state;
* **`graph_valueImport`**, **`graph_valueExport`**: `Lower.graph S c` is an error, for every
  package interface `S`, when `c` imports or exports a value at the top level. So the binaries
  `binGraphX`/`binCompX` read are undefined there, and no algebra term is their reading.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.ValueNodes

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary Silmaril.Wasm.Wac.Lower

/-- A step that fails from every state. -/
def Fails {σ ε : Type} (m : StateT σ (Except ε) Unit) : Prop := ∀ s, ∃ e, m.run s = .error e

theorem forM_error {σ ε α : Type} {f : α → StateT σ (Except ε) Unit} :
    ∀ (l : List α) {x : α}, x ∈ l → Fails (f x) → Fails (l.forM f)
  | [], _, hx, _ => absurd hx List.not_mem_nil
  | y :: l, x, hx, hf => fun s => by
    simp only [List.forM, StateT.run_bind]
    rcases List.mem_cons.1 hx with rfl | hx
    · obtain ⟨e, he⟩ := hf s
      exact ⟨e, by rw [he]; rfl⟩
    · cases hy : (f y).run s with
      | error e => exact ⟨e, rfl⟩
      | ok p =>
        obtain ⟨u, s'⟩ := p
        obtain ⟨e, he⟩ := forM_error l hx hf s'
        exact ⟨e, he⟩

theorem import_value {i : Import} {b : ValueBound} (h : i.desc = .value b) : Fails (import_ i) :=
  fun s => ⟨_, by simp only [import_, h]; rfl⟩

theorem export_value (S : Nat → PkgSig) {e : Binary.Export} (h : e.item.sort = .value) :
    Fails (export_ S e) :=
  fun s => ⟨_, by simp only [export_, h, StateT.run_bind]; rfl⟩

theorem graph_of_fails (S : Nat → PkgSig) {c : Ast} {sec : Section} (hs : sec ∈ c.sections)
    (hf : Fails (section_ S sec)) : ∃ e, graph S c = .error e := by
  unfold graph
  by_cases hp : isProfile c = true
  · obtain ⟨e, he⟩ := forM_error c.sections hs hf {}
    refine ⟨e, ?_⟩
    simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    simp only [bind, Except.bind, he]
  · simp only [Bool.not_eq_true] at hp
    exact ⟨_, by simp only [hp, Bool.not_false, ↓reduceIte]; rfl⟩

/-- **A composition importing a value has no composition graph.** -/
theorem graph_valueImport (S : Nat → PkgSig) {c : Ast} (h : HasValueImport c) :
    ∃ e, graph S c = .error e := by
  obtain ⟨xs, i, b, hs, hi, hv⟩ := h
  exact graph_of_fails S hs (forM_error xs hi (import_value hv))

/-- **A composition exporting a value has no composition graph.** -/
theorem graph_valueExport (S : Nat → PkgSig) {c : Ast} (h : HasValueExport c) :
    ∃ e, graph S c = .error e := by
  obtain ⟨xs, x, hs, hx, hv⟩ := h
  exact graph_of_fails S hs (forM_error xs hx (export_value S hv))

end Silmaril.Wasm.Wac.ValueNodes
