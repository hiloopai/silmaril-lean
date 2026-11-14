module

public import Silmaril.Proofs.Wasi.Cli.Main.Runs
public import Silmaril.Cli.Front.Thms

/-!
# `Command.mainWith` on a WASI host meets `Command.spec`

Proofs for `Silmaril.Wasi.Cli.Main.Thms`.

* `Api.close_mainWith`, `Api.after_eq`: the two programs as sequences of `get-arguments`,
  `get-environment` and the rest.
* **`Api.main_sim`**: under a theory that pins `get-arguments` and `get-environment`, every run
  of `A.main c run` is a run of `A.after c.envVars K`, where `K` is what the front end decides
  on the invocation (`c.finish A.host run (c.outcome i)`).
* **`Api.cliSat_main`**: the component of `A.main c run` satisfies `F (c.spec S)` when the
  bodies satisfy `F (S m)` and printing a line is read as printing it (`Api.EmitOk`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli

open Silmaril.Cli Silmaril.Games
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

variable {I X : Set FnName} {St : Type}

namespace Api

variable (A : Api I)

/-- `A.close` of the front end: `get-environment`, then the front end's decision. -/
theorem close_mainWith (c : Command) (run : Matches → CliM I UInt32) (argv : List String) :
    A.close (c.mainWith A.host run argv) =
      A.env.bind fun e => A.close (c.finish A.host run (interpret c (look c.envVars e) argv)) := by
  unfold Api.close Command.mainWith
  show ((A.env.bind fun e => Prog.pure (Except.ok (look c.envVars e))).bind _).bind _ = _
  rw [prog_bind_assoc, prog_bind_assoc]
  rfl

/-- `A.after` as a sequence. -/
theorem after_eq (vs : List String) (K : CliM I UInt32) :
    A.after vs K = A.args.bind fun _ => A.env.bind fun _ => A.close K := by
  unfold Api.after Api.close
  congr 1
  funext _
  show ((A.env.bind fun e => Prog.pure (Except.ok (look vs e))).bind _).bind _ = _
  rw [prog_bind_assoc, prog_bind_assoc]
  rfl

/-- `A.close` of printing a line and returning `k`: the write, then `finish` with `k`, or `1`
when the write failed. -/
theorem close_putLine (ch : Channel) (s : String) (k : UInt32) :
    A.close (A.putLine ch s >>= fun _ => pure k) =
      (A.put ch (utf8 (s ++ "\n"))).bind fun ok => A.finish (if ok then k else 1) := by
  unfold Api.close Api.putLine
  show (((A.put ch _).bind fun ok =>
      Prog.pure (if ok then Except.ok () else Except.error 1)).bind _).bind _ = _
  rw [prog_bind_assoc, prog_bind_assoc]
  congr 1
  funext ok
  cases ok <;> rfl

/-- The declared variables of the invocation's environment are the front end's. -/
theorem look_env (c : Command) (i : Input) : look c.envVars i.env = c.envOf i := rfl

/-- A prefix of an accepted host view is accepted. -/
theorem accepts_append_left {T : Protocol St WEv} {t u : List WEv}
    (h : T.Accepts (hostView (t ++ u))) : T.Accepts (hostView t) :=
  Protocol.Accepts.of_prefix h (by rw [hostView_append]; exact List.prefix_append _ _)

/-- **The simulation**: under a theory that pins `get-arguments` and `get-environment`, a run
of `A.main c run` is a run of the program with the front end's decision fixed. -/
theorem main_sim {T : Input → Protocol St WEv} (hargs : A.ArgsOk T) (henv : A.EnvOk T)
    {c : Command} {run : Matches → CliM I UInt32} {i : Input} {u : List WEv}
    {r : Option (Option (List Val))} (hr : PRun (A.main c run) u r)
    (hA : (T i).Accepts (hostView u)) :
    PRun (A.after c.envVars (c.finish A.host run (c.outcome i))) u r := by
  rw [after_eq]
  refine PRun.bind_mono hr fun t₁ t₂ a hu h₁ h₂ => ?_
  have ha : a = some i.argv := hargs i t₁ a h₁ (accepts_append_left (hu ▸ hA))
  have h₂' : PRun (A.close (c.mainWith A.host run i.args)) t₂ r := by
    rw [ha] at h₂; exact h₂
  rw [close_mainWith] at h₂'
  refine PRun.bind_mono h₂' fun t₃ t₄ e hu' h₃ h₄ => ?_
  have hA' : (T i).Accepts (hostView (t₁ ++ t₃ ++ t₄)) := by
    rw [List.append_assoc, ← hu', ← hu]; exact hA
  have he : e = i.env := henv i t₁ t₃ e h₃ (accepts_append_left hA')
  rw [he, look_env] at h₄
  exact h₄

/-- The host view of a run of an export call is that of the run. -/
theorem hostView_runTrace (q : (nsig X).Op) (u : List WEv) (r : Option (Option (List Val))) :
    hostView (runTrace q u r) = hostView u ++ hostView (retEv q r) := by
  unfold runTrace
  rw [← hostView_append]
  rfl

/-- **From `Command.mainWith` to the decided program**: the guarantee of the component of
`A.after c.envVars K` (with `K` the front end's decision on `i`) is one of the component of
`A.main c run`. -/
theorem guar_main {T : Input → Protocol St WEv} {V : View} (hX : ∀ q : (nsig X).Op, q.1.1 = V.run)
    (hargs : A.ArgsOk T) (henv : A.EnvOk T) {c : Command} {run : Matches → CliM I UInt32}
    {i : Input} {S S' : Spec}
    (h₀ : (ag (I := I) (X := X) (fun t => (T i).Accepts (hostView t)) (V.Guar S' i)).holds
      (ofBody (A.bodyAfter c.envVars (c.finish A.host run (c.outcome i)))))
    (hS : ∀ o, S' i o → S i o) :
    (ag (I := I) (X := X) (fun t => (T i).Accepts (hostView t)) (V.Guar S i)).holds
      (ofBody (A.body c run)) :=
  guar_of_runs hX h₀ hS fun q u r hr hA =>
    A.main_sim hargs henv hr (accepts_append_left (u := retEv q r)
      (by rw [hostView_append, ← hostView_runTrace]; exact hA))

/-- The front end's decision when it prints: the line and its code. -/
theorem finish_text (c : Command) (run : Matches → CliM I UInt32) {out : Outcome}
    {ch : Channel} {s : String} (h : out.text c = some (ch, s)) :
    c.finish A.host run out =
      (A.putLine ch s >>= fun _ => pure (out.exitCode?.getD 0).toUInt32) := by
  cases out with
  | run m => exact absurd h (by simp [Outcome.text])
  | help p => cases h; rfl
  | version v => cases h; rfl
  | error p e => cases h; rfl

/-- `Command.spec` where the front end prints. -/
theorem spec_text {c : Command} {S : Matches → Spec} {i : Input} {ch : Channel} {s : String}
    (h : (c.outcome i).text c = some (ch, s)) (o : Obs) :
    lineSpec ch s ((c.outcome i).exitCode?.getD 0).toUInt32.toUInt8 i o ↔ c.spec S i o := by
  unfold Command.spec lineSpec
  cases hout : c.outcome i with
  | run m => rw [hout] at h; exact absurd h (by simp [Outcome.text])
  | help p => rw [hout] at h; exact Iff.of_eq (by rw [← h])
  | version v => rw [hout] at h; exact Iff.of_eq (by rw [← h])
  | error p e => rw [hout] at h; exact Iff.of_eq (by rw [← h])

/-- Every outcome but `run` prints. -/
theorem text_of_not_run {c : Command} {out : Outcome} (h : ∀ m, out ≠ .run m) :
    ∃ ch s, out.text c = some (ch, s) := by
  cases out with
  | run m => exact absurd rfl (h m)
  | help p => exact ⟨_, _, rfl⟩
  | version v => exact ⟨_, _, rfl⟩
  | error p e => exact ⟨_, _, rfl⟩

/-- **`Command.mainWith` on a WASI host meets `Command.spec`.** -/
theorem cliSat_main {T : Input → Protocol St WEv} {V : View}
    (hX : ∀ q : (nsig X).Op, q.1.1 = V.run) {F : Spec → Spec}
    (hF : ∀ S S' i, (∀ o, S i o → S' i o) → ∀ o, F S i o → F S' i o)
    (hargs : A.ArgsOk T) (henv : A.EnvOk T) (hemit : A.EmitOk T V F X)
    {c : Command} {run : Matches → CliM I UInt32} {S : Matches → Spec}
    (hrun : ∀ i m, c.outcome i = .run m →
      (ag (I := I) (X := X) (fun t => (T i).Accepts (hostView t)) (V.Guar (F (S m)) i)).holds
        (ofBody (A.bodyAfter c.envVars (run m)))) :
    CliSat (W := ⟨I, X⟩) (ofBody (A.body c run)) T V (F (c.spec S)) := by
  intro i
  by_cases hr : ∃ m, c.outcome i = .run m
  · obtain ⟨m, hm⟩ := hr
    have h₀ := hrun i m hm
    have hK : c.finish A.host run (c.outcome i) = run m := by rw [hm]; rfl
    refine A.guar_main hX hargs henv (hK ▸ h₀) (hF _ _ i fun o ho => ?_)
    exact (spec_of_run hm).2 ho
  · obtain ⟨ch, s, hs⟩ := text_of_not_run (c := c) fun m h => hr ⟨m, h⟩
    have h₀ := hemit i c.envVars ch s ((c.outcome i).exitCode?.getD 0).toUInt32
    rw [← finish_text A c run hs] at h₀
    exact A.guar_main hX hargs henv h₀ (hF _ _ i fun o ho => (spec_text hs o).1 ho)

end Api

end Silmaril.Wasi.Cli

end
