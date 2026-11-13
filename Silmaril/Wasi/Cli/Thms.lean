module

public import Silmaril.Wasi.Cli.Defs
public import Silmaril.Wasi.Host.Thms
public import Silmaril.Cli.Behaviour.Thms

/-!
# WASI `cli` components and CLI behaviour specifications: laws

* **`CliSat.every_host`**: a component satisfying a CLI spec under the theory `T` does so in
  every interaction with every host satisfying `T i`, whatever the host's lower interface: each
  play of the linked system comes from a play of the component whose CLI observation the spec
  allows, with the same export events.
* **`CliSat.mono`**: along refinement of specifications (`S ≤ S'`), through
  `Spec.Partial.mono`; `CliSat.orFail`; `CliSat.of_theory`: under a stronger theory;
  `CliSat.of_agP`: from assume–guarantee protocols (`WasiSat`) whose guarantee implies the CLI
  guarantee.
* `View.seen_le_obs` (what a view sees is a partial view of the observation it reads),
  `View.partial_of`, `View.partial_running`: building a `Spec.Partial` fact for a trace.

The partial-observation layer is the behaviour model's (`Silmaril.Cli.Seen`, `Spec.Partial`,
`Spec.orFail`, with their laws in `Silmaril.Cli.Behaviour.Thms`).
* `toBytes_utf8`: WASI's UTF-8 bytes of a string are the model's; `toBytes_prefix`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli

open Silmaril.Cli Silmaril.Games
open Silmaril.Wasm.Resource (Protocol)

variable {W : World} {St : Type}

/-! ## Partial views of traces -/

/-- **What a view sees is a partial view of what it reads**, ended or not. -/
theorem View.seen_le_obs (V : View) (i : Input) (t : List WEv) : V.seen i t ≼ V.obs i t := by
  refine ⟨List.prefix_rfl, List.prefix_rfl, le_refl _, fun _ h => h, fun h => h, ?_⟩
  intro c hc
  simp only [View.obs, View.seen] at hc ⊢
  simp [hc]

/-- **A trace is allowed when what it reads is**: the usual way to prove a guarantee on a trace
whose run has ended (and the only one needed when the reading is exact). -/
theorem View.partial_of {V : View} {S : Spec} {i : Input} {t : List WEv} (h : S i (V.obs i t)) :
    S.Partial i (V.seen i t) :=
  ⟨_, h, V.seen_le_obs i t⟩

/-- **An unfinished run is allowed when it extends to an allowed observation**: its outputs are
prefixes, its consumption and reads no more, and a refusal it saw is the observation's. -/
theorem View.partial_running {V : View} {S : Spec} {i : Input} {t : List WEv}
    (hd : V.code t = none) {o : Obs} (h : S i o) (hout : V.stdout t <+: o.stdout)
    (herr : V.stderr t <+: o.stderr) (hc : (V.stdin t).length ≤ o.consumed)
    (hr : ∀ p ∈ V.reads t, p ∈ o.reads) (hx : V.refused t = true → o.refused = true) :
    S.Partial i (V.seen i t) :=
  ⟨o, h, hout, herr, hc, hr, hx, fun c hc' => by simp [View.seen, hd] at hc'⟩

/-- **A trace is allowed by `Spec.orFail S`** when its stdout is a prefix of an allowed
observation's and, once the run has ended, what the view reads is allowed or a failure. -/
theorem View.partial_orFail {V : View} {S : Spec} {i : Input} {t : List WEv} {o' : Obs}
    (hS : S i o') (hout : V.stdout t <+: o'.stdout)
    (hd : (V.code t).isSome = true → S i (V.obs i t) ∨ (V.obs i t).exit ≠ 0) :
    (Spec.orFail S).Partial i (V.seen i t) := by
  cases hc : V.code t with
  | none =>
    refine ⟨{ V.obs i t with exit := 1 }, .inr ⟨(by decide : (1 : ExitCode) ≠ 0), o', hS, hout⟩, ?_⟩
    refine ⟨List.prefix_rfl, List.prefix_rfl, le_refl _, fun _ h => h, fun h => h, ?_⟩
    intro c h
    simp [View.seen, hc] at h
  | some c =>
    rcases hd (by simp [hc]) with h | h
    · exact ⟨_, .inl h, V.seen_le_obs i t⟩
    · exact ⟨_, .inr ⟨h, o', hS, hout⟩, V.seen_le_obs i t⟩

@[simp] theorem View.seen_exit (V : View) (i : Input) (t : List WEv) :
    (V.seen i t).exit = V.code t := rfl

@[simp] theorem View.seen_stdout (V : View) (i : Input) (t : List WEv) :
    (V.seen i t).stdout = V.stdout t := rfl

/-! ## Satisfaction -/

/-- **For every host**: in every interaction of `σ` with a host satisfying `T i`, the play of
`σ` behind it is seen as a run that `S` allows on `i`. -/
theorem CliSat.every_host {σ : W.Model} {T : Input → Protocol St WEv} {V : View} {S : Spec}
    (h : CliSat σ T V S) (i : Input) {Y : Sig.{0}} (η : Host Y W.imports)
    (hη : (hostSat (T i).Accepts).holds η) :
    ∀ p ∈ link η σ, ∃ t ∈ σ, xtrace p = expView (wtrace t) ∧ V.Guar S i (wtrace t) := by
  rintro p ⟨s', hs', t, ht, hz⟩
  have hA : (T i).Accepts (hostView (wtrace t)) := htrace_zip hz ▸ hη s' hs'
  exact ⟨t, ht, xtrace_zip hz, h i t ht hA⟩

/-- **Along refinement of the specification.** -/
theorem CliSat.mono {σ : W.Model} {T : Input → Protocol St WEv} {V : View} {S S' : Spec}
    (h : CliSat σ T V S) (hS : S ≤ S') : CliSat σ T V S' :=
  fun i t ht hA hn => (h i t ht hA hn).mono hS

/-- **Failures**: a component that satisfies `S` satisfies `Spec.orFail S`. -/
theorem CliSat.orFail {σ : W.Model} {T : Input → Protocol St WEv} {V : View} {S : Spec}
    (h : CliSat σ T V S) : CliSat σ T V (Spec.orFail S) :=
  h.mono (Spec.le_orFail S)

/-- Under a stronger theory. -/
theorem CliSat.of_theory {St' : Type} {σ : W.Model} {T : Input → Protocol St WEv}
    {T' : Input → Protocol St' WEv} {V : View} {S : Spec} (h : CliSat σ T V S)
    (hT : ∀ i t, (T' i).Accepts t → (T i).Accepts t) : CliSat σ T' V S :=
  fun i t ht hA => h i t ht (hT i _ hA)

/-- **From assume–guarantee protocols**: if `σ` meets `G i` under `T i` (`WasiSat`) and `G i`
implies the CLI guarantee, `σ` satisfies the CLI spec. -/
theorem CliSat.of_agP {St' : Type} {σ : W.Model} {T : Input → Protocol St WEv}
    {G : Input → Protocol St' WEv} {V : View} {S : Spec}
    (h : ∀ i, (agP (I := W.imports) (X := W.exports) (T i) (G i)).holds σ)
    (hG : ∀ i t, (G i).Accepts t → V.Guar S i t) : CliSat σ T V S :=
  fun i t ht hA => hG i _ (h i t ht hA)

/-! ## Bytes -/

/-- **WASI's UTF-8 bytes of a string are the model's.** -/
theorem toBytes_utf8 (s : String) :
    toBytes (s.toUTF8.toList.map fun b => BitVec.ofNat 8 b.toNat) = utf8 s := by
  simp [toBytes, utf8, Function.comp_def]

/-- Prefixes are preserved by `toBytes`. -/
theorem toBytes_prefix {a b : List (BitVec 8)} (h : a <+: b) : toBytes a <+: toBytes b :=
  h.map _

@[simp] theorem toBytes_length (a : List (BitVec 8)) : (toBytes a).length = a.length :=
  List.length_map _

end Silmaril.Wasi.Cli

end
