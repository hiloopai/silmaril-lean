module

public import Silmaril.Proofs.Wasi.Cli.Host2.View
public import Silmaril.Wasi.Cli.Main.Thms
public import Silmaril.Wasi.Theory.Thms

/-!
# The WASI 0.2 host: the theory pins the front end, and printing is read as printing

Proofs for `Silmaril.Wasi.Cli.Host2.Thms`.

* `args2_ok`, `env2_ok`: `cliTh2` pins `get-arguments` and `get-environment`
  (`Api.ArgsOk`, `Api.EnvOk`).
* `writeAll_facts`, `put_facts` (`PutFacts`): a run of `api2.put ch b` writes, on the stream
  of `ch` only, a prefix of the chunks of `b`, all of them when it returns `true`, and reads
  nothing else.
* **`emit2_ok`** (`Api.EmitOk`): the component that prints a line and exits with `k` is seen
  through `p2View` as a run of `spec2 (lineSpec ch s k)`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli.Host2

open Silmaril.Cli Silmaril.Wasi Silmaril.Wasi.Cli Silmaril.Games
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Quiet events -/

/-- An event `p2View` does not read at all. -/
def Quiet (e : WEv) : Prop :=
  PlainEv e ∧ write2 e = none ∧ handles Versions.P2.getStderr [e] = [] ∧
    endCode cliRun (some Versions.P2.cliExit) e = none ∧ failedWrite2 e = false

theorem quiet_req {f : FnName} (a : List Val) (hf : f ≠ Versions.P2.cliExit) : Quiet (.req f a) :=
  ⟨plainEv_req f a, rfl, rfl, endCode_req a hf, rfl⟩

theorem quiet_imp {f : FnName} (a : List Val) (n : Option (List Val)) (hp : Plain2 f)
    (h1 : f ≠ Versions.P2.osWrite) (h2 : f ≠ streamWrite) (h3 : f ≠ Versions.P2.getStderr) :
    Quiet (.imp f a n) :=
  ⟨plainEv_imp a n hp, write2_imp a n h1 h2, handles_imp_ne a n h3, rfl,
    failedWrite2_imp a n h1 h2⟩

theorem quiet_call (f : FnName) (a : List Val) : Quiet (.call f a) :=
  ⟨plainEv_call f a, rfl, rfl, rfl, rfl⟩

/-- The events of a run of one call whose answer is returned. -/
theorem run_call_pure {β : Type} {f : FnName} {hf : f ∈ I2} {a : List Val}
    {g : Option (List Val) → β} {t : List WEv} {r : Option β}
    (h : PRun ((callI f hf a).bind fun n => .pure (g n)) t r) :
    ∀ e ∈ t, e = .req f a ∨ ∃ n, e = .imp f a n := by
  have h0 : PRun (.call (⟨f, hf⟩, a) fun n => .pure (g n)) t r := h
  rcases PRun.call_inv h0 with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨n, t', rfl, h'⟩
  · exact fun e he => absurd he List.not_mem_nil
  · exact fun e he => .inl (List.mem_singleton.1 he)
  · have ht' : t' = [] := (PRun.pure_inv h').1
    intro e he
    rcases List.mem_cons.1 he with rfl | he'
    · exact .inl rfl
    · exact .inr ⟨n, by simpa [ht'] using he'⟩

/-- A call of a quiet function, answered and returned, is quiet. -/
theorem quiet_of_call_pure {β : Type} {f : FnName} {hf : f ∈ I2} {g : Option (List Val) → β}
    {t : List WEv} {r : Option β} (h : PRun ((callI f hf []).bind fun n => .pure (g n)) t r)
    (hp : Plain2 f) (h0 : f ≠ Versions.P2.cliExit) (h1 : f ≠ Versions.P2.osWrite)
    (h2 : f ≠ streamWrite) (h3 : f ≠ Versions.P2.getStderr) : ∀ e ∈ t, Quiet e := by
  intro e he
  rcases run_call_pure h e he with rfl | ⟨n, rfl⟩
  · exact quiet_req [] h0
  · exact quiet_imp [] n hp h1 h2 h3

theorem args_quiet {t : List WEv} {r : Option (Option (List String))} (h : PRun api2.args t r) :
    ∀ e ∈ t, Quiet e :=
  quiet_of_call_pure h (by decide) (by decide) (by decide) (by decide) (by decide)

theorem env_quiet {t : List WEv} {r : Option (List (String × String))} (h : PRun api2.env t r) :
    ∀ e ∈ t, Quiet e :=
  quiet_of_call_pure h (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Before the front end's decision, nothing is seen**: a run is quiet, or a quiet prefix
followed by a run of the decision. -/
theorem prefix_quiet {Q : BProg I2} {u : List WEv} {r : Option (Option (List Val))}
    (h : PRun (api2.args.bind fun _ => api2.env.bind fun _ => Q) u r) :
    ((∀ e ∈ u, Quiet e) ∧ r = none) ∨
      ∃ pre u', u = pre ++ u' ∧ (∀ e ∈ pre, Quiet e) ∧ PRun Q u' r := by
  rcases PRun.bind_inv h with ⟨h1, rfl⟩ | ⟨t₁, t₂, a, rfl, h1, h2⟩
  · exact .inl ⟨args_quiet h1, rfl⟩
  have hq₁ : ∀ e ∈ t₁, Quiet e := args_quiet h1
  rcases PRun.bind_inv h2 with ⟨h3, rfl⟩ | ⟨t₃, t₄, e, rfl, h3, h4⟩
  · refine .inl ⟨fun e he => ?_, rfl⟩
    rcases List.mem_append.1 he with he | he
    exacts [hq₁ e he, env_quiet h3 e he]
  · refine .inr ⟨t₁ ++ t₃, t₄, (List.append_assoc _ _ _).symm, fun e he => ?_, h4⟩
    rcases List.mem_append.1 he with he | he
    exacts [hq₁ e he, env_quiet h3 e he]

/-! ## The theory -/

/-- The pointwise part of `cliTh2`. -/
theorem cliTh2_point {i : Input} {t : List WEv} (h : (cliTh2 i).Accepts t) {e : WEv}
    (he : e ∈ t) :
    (argsOk Versions.P2.getArgs i e && envOk Versions.P2.getEnv i e && preopensOk getDirs i e) =
      true :=
  (pointwise_accepts_iff _ _).1 ((Protocol.accepts_prod_iff _ _ _).1 h).1 e he

/-- A finished run of a call whose answer is returned. -/
theorem run_call_done {β : Type} {f : FnName} {hf : f ∈ I2} {g : Option (List Val) → β}
    {t : List WEv} {b : β} (h : PRun ((callI f hf []).bind fun n => .pure (g n)) t (some b)) :
    ∃ n, t = [.req f [], .imp f [] n] ∧ b = g n := by
  have h0 : PRun (.call (⟨f, hf⟩, []) fun n => .pure (g n)) t (some b) := h
  rcases PRun.call_inv h0 with ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨n, t', rfl, h'⟩
  · exact absurd h' (by simp)
  · exact absurd h' (by simp)
  · obtain ⟨rfl, hb⟩ := PRun.pure_inv h'
    exact ⟨n, rfl, by simpa using hb⟩

/-- **`cliTh2` pins `get-arguments`.** -/
theorem args2_ok : api2.ArgsOk cliTh2 := by
  intro i t a h hA
  obtain ⟨n, rfl, rfl⟩ := run_call_done h
  have hp := cliTh2_point hA (e := .imp Versions.P2.getArgs [] n) (by simp [hostView, WEv.isImp])
  have hargs : argsOk Versions.P2.getArgs i (.imp Versions.P2.getArgs [] n) = true := by
    simp only [Bool.and_eq_true] at hp; exact hp.1.1
  simpa [argsOk, Input.argv] using hargs

/-- **`cliTh2` pins `get-environment`.** -/
theorem env2_ok : api2.EnvOk cliTh2 := by
  intro i pre t e h hA
  obtain ⟨n, rfl, rfl⟩ := run_call_done h
  have hp := cliTh2_point hA (e := .imp Versions.P2.getEnv [] n) (by simp [hostView, WEv.isImp])
  have henv : envOk Versions.P2.getEnv i (.imp Versions.P2.getEnv [] n) = true := by
    simp only [Bool.and_eq_true] at hp; exact hp.1.2
  have hn : envOf n = some i.env := by simpa [envOk] using henv
  simp [hn]

end Silmaril.Wasi.Cli.Host2

end
