module

public import Silmaril.Project.WasmP3Rust.CliSpec.Defs
public import Silmaril.Project.WasmP3Rust.StdioK.Thms
public import Silmaril.Project.WasmP3Rust.TasksP3.Thms
public import Silmaril.Wasi.Cli.Thms

/-!
# `echo.wasm` and `cat.wasm` satisfy their CLI behaviour specifications

* `exitOf_zero`: an exit code `0` in the WASI 0.3 view means `run` returned `ok` (`runOk`).
* **`echoG1_guar`**: `echo`'s WASI guarantee `echoG1 (i.prog :: i.args)` implies the CLI
  guarantee of `orFail echoSpec` through `p3View`.
* **`echoCli_of`**: `Task.echoPrintsX den` for every argument list gives `Task.echoCli den`;
  **`echoCli_model`**: proved for `DenX.den` with the core model `stdioK echoPlan`;
  `echoCli_of_core`: for every core semantics with `Task.echoCore`; `echoCli_every_host`.
* **The reduction of `Task.echoCore`**: `echoLines_of_core` (`Task.echoCore Ks` gives the
  behavioural target `Task.echoLines Ks`), `echoCli_of_lines` (which is all `Task.echoCli`
  needs), `echoLines_model`.
* **`catGX_guar`**: `cat`'s WASI guarantee `catGX`, on a trace whose stdin is a prefix of
  `i.stdin`, implies the CLI guarantee of `orFail catNow` through `p3xView`;
  `stdinBytesX_hostView`: the stdin reading sees only the host's answers.
* **`catCli_of`**: `Task.catCopiesX den` gives `Task.catCli den`; **`catCli_model`**: proved
  for `DenX.den` with `stdioK catPlan`; `catCli_of_core` (under `Task.catCore`);
  **`catCli_every_host`**: in every interaction with every host of `catCliTh i`, the play of
  `cat.wasm` is seen as a run `orFail catNow` allows.
* `catNow_inf_consumesAll`: a run of `catNow` that consumed all of stdin is a run of `catSpec`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust

open Silmaril.Cli Silmaril.Wasi Silmaril.Wasi.Cli Silmaril.Wasi.Versions.P3 Silmaril.Games
open Silmaril.Cli.Spec (orFail le_orFail)
open Silmaril.Project.WasmP3Rust.DenX (p3xWorld)
open Silmaril.Project.WasmP3Rust.StdioK (stdioK echoPlan catPlan)
open Silmaril.Wasm.Component.BinaryP3 (Ast)
open Silmaril.Cli.Io.Examples (echoSpec echoOut catSpec)

/-- An exit code `0` read by `p3View` comes from a return of `run` with an `ok` result. -/
theorem exitOf_zero {t : List WEv} (h : exitOf run3 none t = some 0) : runOk t = true := by
  obtain ⟨e, he, hc⟩ := List.exists_of_findSome?_eq_some h
  rcases e with ⟨f, a⟩ | ⟨f, a, r⟩ | ⟨f, a⟩ | ⟨f, a, r⟩
  · rcases a with _ | ⟨v, _ | _⟩ <;> simp [endCode] at hc
  · simp [endCode] at hc
  · simp [endCode] at hc
  · have hf : f = run3 := by by_contra hf; simp [endCode, hf] at hc
    have hr : retCode r = 0 := by simpa [endCode, hf] using hc
    rcases r with _ | ⟨_ | ⟨v, _ | _⟩⟩
    · simp [retCode, trapExit] at hr
    · simp [retCode] at hr
    · have hv : resultOk v = true := by
        by_contra hv; simp [retCode, codeOf, hv] at hr
      exact List.any_eq_true.2 ⟨_, he, by simp [hf, hv]⟩
    · simp [retCode] at hr

/-- What `p3View` (with any stdin reading) reads: stdout, nothing on stderr, no file. -/
theorem p3View_obs (st : List WEv → Bytes) (i : Input) (t : List WEv) :
    (p3View none st).obs i t =
      { stdout := toBytes (stdoutBytes t), exit := (exitOf run3 none t).getD 0,
        consumed := (st t).length, fs := i.fs } := rfl

/-- **A trace seen through `p3View`** is a partial view of a run `S` allows when it extends one
(`hrun`, while `run` has not returned) and, once it has, what it reads is allowed (`hend`). -/
theorem p3View_partial {st : List WEv → Bytes} {S : Spec} {i : Input} {t : List WEv} {o : Obs}
    (ho : S i o) (hout : toBytes (stdoutBytes t) <+: o.stdout) (hc : (st t).length ≤ o.consumed)
    (hend : ∀ c, exitOf run3 none t = some c → S i ((p3View none st).obs i t)) :
    S.Partial i ((p3View none st).seen i t) := by
  rcases hx : exitOf run3 none t with _ | c
  · exact View.partial_running hx ho hout List.nil_prefix hc (fun _ hp => nomatch hp)
      (fun h => nomatch h)
  · exact View.partial_of (hend c hx)

/-- What a trace-predicate guarantee says of a trace it accepts. -/
theorem onceG_holds {P : List WEv → Bool} {t : List WEv} (h : (onceG P).Accepts t)
    (hn : runCalls t ≤ 1) (hne : t ≠ []) : P t = true := by
  have h1 : (!decide (runCalls t ≤ 1) || P t) = true :=
    ofTraces_run_some (P := fun t => !decide (runCalls t ≤ 1) || P t) [] t h hne
  simpa [hn] using h1

/-! ## echo -/

/-- `echo`'s line, as WASI bytes. -/
abbrev echoMsg (i : Input) : List (BitVec 8) :=
  Silmaril.Project.WasmP3Rust.utf8 (" ".intercalate ((i.prog :: i.args).drop 1) ++ "\n")

/-- The line in the model's bytes. -/
theorem toBytes_echoMsg (i : Input) : toBytes (echoMsg i) = echoOut i.args :=
  toBytes_utf8 _

/-- The finished run that prints the whole line. -/
def echoDone (i : Input) : Obs := { stdout := echoOut i.args, fs := i.fs }

theorem echoDone_spec (i : Input) : echoSpec i (echoDone i) :=
  ⟨rfl, rfl, rfl, rfl, rfl, Nat.zero_le _, rfl⟩

/-- **`echo`'s WASI guarantee implies its CLI guarantee.** -/
theorem echoG1_guar (i : Input) (t : List WEv) (h : (echoG1 (i.prog :: i.args)).Accepts t) :
    (p3View).Guar (orFail echoSpec) i t := by
  intro hn
  have hrun : runCalls t ≤ 1 := hn
  have hP1 : stdoutBytes t <+: echoMsg i := by
    rcases eq_or_ne t [] with rfl | hne
    · exact List.nil_prefix
    · have hP : printsP (echoMsg i) t = true := onceG_holds h hrun hne
      simp only [printsP, Bool.and_eq_true] at hP
      exact List.isPrefixOf_iff_prefix.1 hP.1
  have hP2 : runOk t = true → stdoutBytes t = echoMsg i := fun hr => by
    have hne : t ≠ [] := by rintro rfl; simp [runOk] at hr
    have hP : printsP (echoMsg i) t = true := onceG_holds h hrun hne
    exact (by simpa [printsP, hr] using hP : _ ∧ _).2
  have hout : toBytes (stdoutBytes t) <+: echoOut i.args :=
    toBytes_echoMsg i ▸ toBytes_prefix hP1
  refine p3View_partial (le_orFail _ _ _ (echoDone_spec i)) hout (Nat.zero_le _) fun c hx => ?_
  rw [p3View_obs]
  by_cases hc : c = 0
  · have hs : toBytes (stdoutBytes t) = echoOut i.args := by
      rw [hP2 (exitOf_zero (hc ▸ hx)), toBytes_echoMsg]
    exact .inl ⟨hs, rfl, by simp [hx, hc], rfl, rfl, Nat.zero_le _, rfl⟩
  · exact .inr ⟨by simpa [hx] using hc, echoDone i, echoDone_spec i, hout⟩

/-- **From `Task.echoPrintsX` for every argument list.** -/
theorem echoCli_of {den : Ast → p3xWorld.Model} (h : ∀ args, Task.echoPrintsX den args) :
    Task.echoCli den := by
  obtain ⟨c, hc, -⟩ := h []
  refine ⟨c, hc, CliSat.of_agP (G := fun i => echoG1 (i.prog :: i.args)) (fun i => ?_)
    echoG1_guar⟩
  obtain ⟨c', hc', hs⟩ := h (i.prog :: i.args)
  have hcc : c' = c := Except.ok.inj (hc'.symm.trans hc)
  exact hcc ▸ hs

/-- **`echo.wasm` satisfies `echo`'s CLI specification**, under `DenX.den` with the core model
`stdioK echoPlan`. -/
theorem echoCli_model : Task.echoCli (DenX.den fun _ => stdioK echoPlan) :=
  echoCli_of StdioK.echo_prints_model

/-- **The same under every core semantics that refines the model** (`Task.echoCore`). -/
theorem echoCli_of_core {Ks : Ast → DenX.CoreExecX} (h : StdioK.Task.echoCore Ks) :
    Task.echoCli (DenX.den Ks) :=
  echoCli_of (StdioK.echo_prints_of_core h)

/-- **The reduction of `Task.echoCore`**: refining the model's denotation gives the behavioural
target. -/
theorem echoLines_of_core {Ks : Ast → DenX.CoreExecX} (h : StdioK.Task.echoCore Ks) :
    Task.echoLines Ks :=
  StdioK.echo_prints_of_core h

/-- **The behavioural target is enough** for the CLI theorem. -/
theorem echoCli_of_lines {Ks : Ast → DenX.CoreExecX} (h : Task.echoLines Ks) :
    Task.echoCli (DenX.den Ks) :=
  echoCli_of h

/-- The core model meets the behavioural target. -/
theorem echoLines_model : Task.echoLines fun _ => stdioK echoPlan :=
  StdioK.echo_prints_model

/-- **For every host**: under the core model, in every interaction of `echo.wasm` with a host of
`echoCliTh i`, the component's play is seen as a run `orFail echoSpec` allows. -/
theorem echoCli_every_host :
    ∃ c : Ast, Silmaril.Wasm.Component.BinaryP3.parse (arrOf Echo.File.bytes) = .ok c ∧
      ∀ (i : Input) (Y : Sig.{0}) (η : Host Y p3xWorld.imports),
        (hostSat (echoCliTh i).Accepts).holds η →
        ∀ p ∈ link η (DenX.den (fun _ => stdioK echoPlan) c),
          ∃ t ∈ DenX.den (fun _ => stdioK echoPlan) c, xtrace p = expView (wtrace t) ∧
            (p3View).Guar (orFail echoSpec) i (wtrace t) :=
  let ⟨c, hc, hs⟩ := echoCli_model
  ⟨c, hc, fun i _ η hη => hs.every_host i η hη⟩

/-! ## cat -/

/-- The stdin scan sees only import answers. -/
theorem stdinScanX_hostView (rs : List Nat) (t : List WEv) :
    stdinScanX rs (hostView t) = stdinScanX rs t := by
  induction t generalizing rs with
  | nil => rfl
  | cons e t ih =>
    rcases e with ⟨f, a⟩ | ⟨f, a, r⟩ | ⟨f, a⟩ | ⟨f, a, r⟩
    · exact ih rs
    · show (inStep rs _).2 ++ stdinScanX (inStep rs _).1 (hostView t) = _
      rw [ih]
      rfl
    · exact ih rs
    · exact ih rs

/-- **The stdin reading sees only the host's answers.** -/
theorem stdinBytesX_hostView (t : List WEv) : stdinBytesX (hostView t) = stdinBytesX t :=
  stdinScanX_hostView [] t

/-- The finished run that copied the stdin bytes `d`. -/
def catDone (i : Input) (d : Bytes) : Obs := { stdout := d, consumed := d.length, fs := i.fs }

theorem catDone_spec {i : Input} {d : Bytes} (h : d <+: i.stdin) : catNow i (catDone i d) :=
  ⟨List.prefix_iff_eq_take.1 h, h.length_le, rfl, rfl, rfl, rfl, rfl⟩

/-- **`cat`'s WASI guarantee implies its CLI guarantee**, on a trace whose stdin is a prefix of
`i.stdin`. -/
theorem catGX_guar (i : Input) (t : List WEv) (h : catGX.Accepts t)
    (hs : toBytes (stdinBytesX t) <+: i.stdin) : p3xView.Guar (orFail catNow) i t := by
  intro hn
  have hrun : runCalls t ≤ 1 := hn
  have hQ1 : stdoutBytes t <+: stdinBytesX t := by
    rcases eq_or_ne t [] with rfl | hne
    · exact List.nil_prefix
    · have hQ : ((stdoutBytes t).isPrefixOf (stdinBytesX t) &&
          (!runOk t || stdoutBytes t == stdinBytesX t)) = true := onceG_holds h hrun hne
      simp only [Bool.and_eq_true] at hQ
      exact List.isPrefixOf_iff_prefix.1 hQ.1
  have hQ2 : runOk t = true → stdoutBytes t = stdinBytesX t := fun hr => by
    have hne : t ≠ [] := by rintro rfl; simp [runOk] at hr
    have hQ : ((stdoutBytes t).isPrefixOf (stdinBytesX t) &&
        (!runOk t || stdoutBytes t == stdinBytesX t)) = true := onceG_holds h hrun hne
    exact (by simpa [hr] using hQ : _ ∧ _).2
  have hout : toBytes (stdoutBytes t) <+: toBytes (stdinBytesX t) := toBytes_prefix hQ1
  have hdone : catNow i (catDone i (toBytes (stdinBytesX t))) := catDone_spec hs
  unfold p3xView
  refine p3View_partial (le_orFail _ _ _ hdone) hout (le_refl _) fun c hx => ?_
  rw [p3View_obs]
  by_cases hc : c = 0
  · have heq : toBytes (stdoutBytes t) = toBytes (stdinBytesX t) := by
      rw [hQ2 (exitOf_zero (hc ▸ hx))]
    exact .inl ⟨heq.trans (List.prefix_iff_eq_take.1 hs), by simpa using hs.length_le, rfl,
      by simp [hx, hc], rfl, rfl, rfl⟩
  · exact .inr ⟨by simpa [hx] using hc, _, hdone, hout⟩

/-- The stdin theory gives the prefix. -/
theorem stdinTh_prefix {i : Input} {t : List WEv} (h : (stdinTh i).Accepts (hostView t)) :
    toBytes (stdinBytesX t) <+: i.stdin := by
  rw [← stdinBytesX_hostView]
  rcases eq_or_ne (hostView t) [] with h0 | hne
  · rw [h0]
    exact List.nil_prefix
  · have h1 : (toBytes (stdinBytesX (hostView t))).isPrefixOf i.stdin = true :=
      ofTraces_run_some (P := fun t => (toBytes (stdinBytesX t)).isPrefixOf i.stdin) [] _ h hne
    exact List.isPrefixOf_iff_prefix.1 h1

/-- **From `Task.catCopiesX`.** -/
theorem catCli_of {den : Ast → p3xWorld.Model} (h : Task.catCopiesX den) : Task.catCli den := by
  obtain ⟨c, hc, hs⟩ := h
  refine ⟨c, hc, fun i t ht hA => ?_⟩
  have hA' : stdoutTh3x.Accepts (hostView (wtrace t)) ∧ (stdinTh i).Accepts (hostView (wtrace t)) :=
    (Silmaril.Wasm.Resource.Protocol.accepts_prod_iff _ _ _).1 hA
  exact catGX_guar i _ (hs t ht hA'.1) (stdinTh_prefix hA'.2)

/-- **`cat.wasm` satisfies `cat`'s CLI specification**, under `DenX.den` with the core model
`stdioK catPlan`. -/
theorem catCli_model : Task.catCli (DenX.den fun _ => stdioK catPlan) :=
  catCli_of StdioK.cat_copies_model

/-- The same under every core semantics that refines the model (`Task.catCore`, open). -/
theorem catCli_of_core {Ks : Ast → DenX.CoreExecX} (h : StdioK.Task.catCore Ks) :
    Task.catCli (DenX.den Ks) :=
  catCli_of (StdioK.cat_copies_of_core h)

/-- **For every host**: under the core model, in every interaction of `cat.wasm` with a host of
`catCliTh i`, the component's play is seen as a run `orFail catNow` allows. -/
theorem catCli_every_host :
    ∃ c : Ast, Silmaril.Wasm.Component.BinaryP3.parse (arrOf Cat.File.bytes) = .ok c ∧
      ∀ (i : Input) (Y : Sig.{0}) (η : Host Y p3xWorld.imports),
        (hostSat (catCliTh i).Accepts).holds η →
        ∀ p ∈ link η (DenX.den (fun _ => stdioK catPlan) c),
          ∃ t ∈ DenX.den (fun _ => stdioK catPlan) c, xtrace p = expView (wtrace t) ∧
            p3xView.Guar (orFail catNow) i (wtrace t) :=
  let ⟨c, hc, hs⟩ := catCli_model
  ⟨c, hc, fun i _ η hη => hs.every_host i η hη⟩

/-- A run `catNow` allows that consumed all of stdin is a run of `catSpec`. -/
theorem catNow_inf_consumesAll : catNow ⊓ Spec.consumesAll ≤ catSpec := by
  rintro i o ⟨⟨hout, -, herr, hx, hfs, hr, hlog⟩, hall⟩
  have hall' : o.consumed = i.stdin.length := hall
  refine ⟨⟨?_, herr, hx, hfs, hr, hall'.le, hlog⟩, hall⟩
  rw [hout, hall', List.take_length]

end Silmaril.Project.WasmP3Rust

end
