module

public import Silmaril.Wasm.Logic.Open.Defs

/-!
# Open modules: import stubs, host monotonicity and closing

* host-call redexes (`SingleThreaded.decompose?`): a host-free step has none
  (`decompose?_none_of_step`), a redex is not an exit (`not_exits_of_redex`), and
  a redex steps with each outcome of the host (`redex_step_ret`,
  `redex_step_div`);
* `FSpecAt.stub`: under the most general environment `specHost bind Γi`, an import
  stub meets the import specification (`stubSpec`), so a call of an import is
  proved with the ordinary call rule `Hoare.Safe.call`;
* `Step.host_mono` and `Safe.host_mono`: safety moves to any host relation that
  is **sound** (each of its outcomes is allowed) and **live** (it has an outcome
  wherever the larger one has); hence `ModuleSat.valid_host`: a module meeting its
  specifications meets them in the closed world for every concrete environment
  that is sound and live for its imports.

Built on silmaril-lean's host-call decomposition
(`Silmaril/Wasm/SingleThreaded/Agreement.lean`: `Step.split_host`,
`decompose?_redex`, `decompose?_wrap`, `Ctx.step_fill`;
`Silmaril/Wasm/SingleThreaded/Thread.lean`: `decompose?_sound`;
`Silmaril/Wasm/SingleThreaded/NoRedex.lean`: `Step.noRedex`). A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Open

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded (decompose?)
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Strategy (resultOutcome)

variable {H : Type} {P : Profile}

/-! ## Host-call redexes -/

/-- A host-free step has no host-call redex. -/
theorem decompose?_none_of_step {c c' : Config H} (h : Step P noHost c c') :
    decompose? c.store c.code = none :=
  SingleThreaded.decompose?_none_of_noRedex (SingleThreaded.Step.noRedex h)

/-- A host-call redex steps to the host's result. -/
theorem redex_step_ret {host : HostSemantics H} {c : Config H} {E : SingleThreaded.Ctx} {a : Nat}
    {h : H} {args : List Val} (hd : decompose? c.store c.code = some (E, a, h, args))
    {s' : Store H} {r : Result} (hr : host h c.store args (.returned s' r)) :
    Step P host c ⟨s', c.frame, E.fill r.toAdmin⟩ := by
  rcases c with ⟨s, f, code⟩
  obtain ⟨fi, yy, ps, rs, hf, hc, hyy, he, hn, hcode⟩ := SingleThreaded.decompose?_sound hd
  have hstep : Step P host ⟨s, f, E.fill (vals args ++ [.ref (.func a), yy])⟩
      ⟨s', f, E.fill r.toAdmin⟩ :=
    E.step_fill (fun _ => Step.callRefHost hyy hf he hn hc hr) f
  have hcode' : code = E.fill (vals args ++ [.ref (.func a), yy]) := hcode
  show Step P host ⟨s, f, code⟩ ⟨s', f, E.fill r.toAdmin⟩
  rw [hcode']
  exact hstep

/-- A host-call redex stutters when the host diverges. -/
theorem redex_step_div {host : HostSemantics H} {c : Config H} {E : SingleThreaded.Ctx} {a : Nat}
    {h : H} {args : List Val} (hd : decompose? c.store c.code = some (E, a, h, args))
    (hr : host h c.store args .diverged) : Step P host c c := by
  rcases c with ⟨s, f, code⟩
  obtain ⟨fi, yy, ps, rs, hf, hc, hyy, he, hn, hcode⟩ := SingleThreaded.decompose?_sound hd
  have hstep : Step P host ⟨s, f, E.fill (vals args ++ [.ref (.func a), yy])⟩
      ⟨s, f, E.fill (vals args ++ [.ref (.func a), yy])⟩ :=
    E.step_fill (fun _ => Step.callRefHostDiv hyy hf he hn hc hr) f
  have hcode' : code = E.fill (vals args ++ [.ref (.func a), yy]) := hcode
  rw [hcode']
  exact hstep

/-- A host-call redex steps whenever the host has an outcome. -/
theorem redex_progress {host : HostSemantics H} {c : Config H} {E : SingleThreaded.Ctx} {a : Nat}
    {h : H} {args : List Val} (hd : decompose? c.store c.code = some (E, a, h, args))
    {o : Host.Outcome (Store H) Result} (ho : host h c.store args o) : ∃ c', Step P host c c' := by
  cases o with
  | returned s' r => exact ⟨_, redex_step_ret hd ho⟩
  | diverged => exact ⟨_, redex_step_div hd ho⟩

/-- A host-call redex is not an exit (it stutters under a diverging host, while an
exit that steps shrinks). -/
theorem not_exits_of_redex (P : Profile) {s : Store H} {code : List Admin} {E : SingleThreaded.Ctx}
    {a : Nat} {h : H} {args : List Val} (hd : decompose? s code = some (E, a, h, args))
    (o : Outcome) : ¬ Exits o code := fun hex => by
  have hstep : Step P (fun _ _ _ _ => True : HostSemantics H) ⟨s, {}, code⟩ ⟨s, {}, code⟩ :=
    redex_step_div (c := ⟨s, {}, code⟩) hd trivial
  exact lt_irrefl _ (hex.step hstep).2.2.2

/-- The steps of a host-call redex: the host returns or diverges. -/
theorem redex_step_inv {host : HostSemantics H} {c c' : Config H} {E : SingleThreaded.Ctx}
    {a : Nat} {h : H} {args : List Val} (hd : decompose? c.store c.code = some (E, a, h, args))
    (hst : Step P host c c') :
    (∃ s' r, host h c.store args (.returned s' r) ∧ c' = ⟨s', c.frame, E.fill r.toAdmin⟩) ∨
      (host h c.store args .diverged ∧ c' = c) := by
  rcases SingleThreaded.Step.split_host hst with h0 | ⟨E', a', h', args', hd', hr⟩
  · exact absurd ((decompose?_none_of_step h0).symm.trans hd) (by simp)
  · have heq : (E', a', h', args') = (E, a, h, args) := Option.some.inj (hd'.symm.trans hd)
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
    exact hr

/-! ## Import stubs -/

/-- The code of a call below `vs₀`, as a context filled with the call. -/
theorem stub_code (vs₀ args : List Val) (a : Nat) (c : Admin) :
    vals vs₀ ++ vals args ++ [.ref (.func a), c] =
      ((SingleThreaded.Ctx.top [] []).wrap vs₀ []).fill (vals args ++ [.ref (.func a), c]) := by
  simp [SingleThreaded.Ctx.fill_wrap, SingleThreaded.Ctx.fill, vals]

/-- The context of a stub call, filled. -/
theorem stub_fill (vs₀ : List Val) (xs : List Admin) :
    ((SingleThreaded.Ctx.top [] []).wrap vs₀ []).fill xs = vals vs₀ ++ xs := by
  simp [SingleThreaded.Ctx.fill_wrap, SingleThreaded.Ctx.fill, vals]

/-- The host-call redex of a stub call. -/
theorem decompose?_stub {s : Store H} {vs₀ args : List Val} {a : Nat} {c : Admin}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {h : H} (hc : c.IsCallRef)
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs)) (hn : args.length = ps.length)
    (hcode : fi.code = .host h) :
    decompose? s (vals vs₀ ++ vals args ++ [.ref (.func a), c]) =
      some ((SingleThreaded.Ctx.top [] []).wrap vs₀ [], a, h, args) := by
  have hd : decompose? s (vals vs₀ ++ (vals args ++ [.ref (.func a), c]) ++ []) =
      some ((SingleThreaded.Ctx.top [] []).wrap vs₀ [], a, h, args) :=
    SingleThreaded.decompose?_wrap vs₀ [] (SingleThreaded.decompose?_redex hc hf he hn hcode)
  simpa using hd

/-- A call that returned `r` below `vs₀` is an exit of the call postcondition. -/
theorem result_exit {host : HostSemantics H} {n : Nat} {vs₀ : List Val} {s' : Store H} {f : Frame}
    {R : Store H → Outcome → Prop} (r : Result) (hR : R s' (resultOutcome r)) :
    Safe P host (callPost f vs₀ R) n ⟨s', f, vals vs₀ ++ r.toAdmin⟩ := by
  rcases r with res | a | _
  · exact Safe.of_exits (o := .normal (vs₀ ++ res)) (by simp [Exits, Result.toAdmin, vals])
      ⟨rfl, .inl ⟨res, rfl, hR⟩⟩
  · exact Safe.of_exits (o := .throw a) ⟨vs₀, [], by simp [Result.toAdmin, throwing]⟩
      ⟨rfl, .inr (.inr ⟨a, rfl, hR⟩)⟩
  · exact Safe.of_exits (o := .trap) ⟨vs₀, [], by simp [Result.toAdmin]⟩ ⟨rfl, .inr (.inl ⟨rfl, hR⟩)⟩

/-- **The stub rule.** Under the most general environment of `Γi`, an import stub
with host code `h` meets the specification `Γi (bind h)` (when it is in the
store and called with its arity), for every number of steps. -/
theorem FSpecAt.stub {bind : H → Nat} {Γi : Ctx H} {a : Nat} {h : H} {S : FSpec H}
    (hS : Γi (bind h) = some S) : ∀ n, FSpecAt P (specHost bind Γi) n a (stubSpec a h S)
  | 0 => fun _ _ _ _ _ _ _ => trivial
  | n + 1 => fun s args ⟨⟨fi, ps, rs, hf, hcode, he, hn⟩, hpre⟩ f vs₀ c hc => by
    have hd : decompose? s (vals vs₀ ++ vals args ++ [.ref (.func a), c]) =
        some ((SingleThreaded.Ctx.top [] []).wrap vs₀ [], a, h, args) :=
      decompose?_stub hc hf he hn hcode
    refine Safe.of_step (redex_progress (c := ⟨s, f, _⟩) hd (o := .diverged) ⟨S, hS, hpre, trivial⟩)
      fun c' hst => ?_
    rcases redex_step_inv hd hst with ⟨s', r, ⟨S', hS', -, hpost⟩, rfl⟩ | ⟨-, rfl⟩
    · obtain rfl : S' = S := Option.some.inj (hS'.symm.trans hS)
      rw [stub_fill]
      exact result_exit r hpost
    · exact FSpecAt.stub hS n s args ⟨⟨fi, ps, rs, hf, hcode, he, hn⟩, hpre⟩ f vs₀ c hc

/-! ## Changing the host relation -/

/-- Steps under a smaller host relation are steps under a larger one. -/
theorem Step.host_mono {host host' : HostSemantics H}
    (hsub : ∀ h s args o, host h s args o → host' h s args o) {c c' : Config H}
    (hst : Step P host c c') : Step P host' c c' := by
  rcases SingleThreaded.Step.split_host hst with h0 | ⟨E, a, h, args, hd, ⟨s', r, hr, rfl⟩ | ⟨hr, rfl⟩⟩
  · exact Step.of_noHost host' h0
  · exact redex_step_ret hd (hsub _ _ _ _ hr)
  · exact redex_step_div hd (hsub _ _ _ _ hr)

/-- Progress moves to a live host relation. -/
theorem Step.progress_of_live {host host' : HostSemantics H}
    (hlive : ∀ h s args o, host' h s args o → ∃ o', host h s args o') {c c' : Config H}
    (hst : Step P host' c c') : ∃ c'', Step P host c c'' := by
  rcases SingleThreaded.Step.split_host hst with h0 | ⟨E, a, h, args, hd, ⟨s', r, hr, -⟩ | ⟨hr, -⟩⟩
  · exact ⟨c', Step.of_noHost host h0⟩
  · obtain ⟨o, ho⟩ := hlive _ _ _ _ hr
    exact redex_progress hd ho
  · obtain ⟨o, ho⟩ := hlive _ _ _ _ hr
    exact redex_progress hd ho

/-- **Safety moves to a sound and live host relation.** -/
theorem Safe.host_mono {host host' : HostSemantics H}
    (hsub : ∀ h s args o, host h s args o → host' h s args o)
    (hlive : ∀ h s args o, host' h s args o → ∃ o', host h s args o') :
    ∀ {n : Nat} {Q : Post H} {c : Config H}, Safe P host' Q n c → Safe P host Q n c
  | 0, _, _, _ => trivial
  | _ + 1, _, _, .inl hx => .inl hx
  | _ + 1, _, _, .inr ⟨⟨_, hc'⟩, hall⟩ => .inr ⟨Step.progress_of_live hlive hc',
      fun c'' h => Safe.host_mono hsub hlive (hall c'' (Step.host_mono hsub h))⟩

/-- **Closing a module.** If a module meets its specifications under its imports,
then for every concrete environment `host` that is sound (each outcome is allowed
by the import specification) and live (it has an outcome for every call meeting
an import precondition), the exports are valid in the closed world `Step P host`. -/
theorem ModuleSat.valid_host {M : OMod H} {bind : H → Nat} {Γi Γe : Ctx H}
    (hm : ModuleSat P M bind Γi Γe) {host : HostSemantics H}
    (hsound : ∀ h s args o, host h s args o → specHost bind Γi h s args o)
    (hlive : ∀ h s args S, Γi (bind h) = some S → S.pre s args → ∃ o, host h s args o) :
    Ctx.Valid P host Γe := fun n a S hS s args hpre f vs₀ c hc =>
  Safe.host_mono hsound (fun _ _ _ _ ⟨S', hS', hpre', _⟩ => hlive _ _ _ S' hS' hpre')
    (hm.2 n a S hS s args hpre f vs₀ c hc)

/-- **Guarded proofs of a module** (mutual recursion inside the module, Löb
induction): the export specifications hold for `n + 1` steps whenever they hold
for `n` steps, under the most general environment of the imports. -/
theorem ModuleSat.of_step {M : OMod H} {bind : H → Nat} {Γi Γe : Ctx H}
    (hshape : ∀ a S, Γe a = some S → (M.funcs a).isSome ∧ ∀ s args, S.pre s args → M.Has s)
    (h : ∀ n, Ctx.ValidAt P (specHost bind Γi) n Γe → Ctx.ValidAt P (specHost bind Γi) (n + 1) Γe) :
    ModuleSat P M bind Γi Γe :=
  ⟨hshape, Ctx.valid_of_step h⟩

end Silmaril.Wasm.Logic.Open
