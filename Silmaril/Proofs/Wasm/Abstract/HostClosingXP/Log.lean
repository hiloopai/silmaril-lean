module

public import Silmaril.Wasm.Abstract.HostClosingXP.Defs
public import Silmaril.Wasm.Abstract.HostCall.Thms
public import Silmaril.Wasm.Interp.HostEvalP.Thms
public import Silmaril.Wasm.Cfg.Region.Thms

/-!
# Logged Core runs for the canonical relation (proofs)

The logged form of the Core side of `Interp.PendSim` (`CoreGoodP`, postcondition `MatchP`): a
Core run whose host events (`EvRun`) are **exactly** a given log.

* `WPL`: a logged Core run to a final form satisfying a postcondition (`WP` with its events);
* `wpl_wrap`: the logged run of a hole inside a context lifting every labelled step (a sequence
  context, a label, a handler, a frame), then a host-free exit from the context (a `WP` at the
  empty host `NH`, from the lemmas of `Interp.Control`, `Interp.EHSim`, `Interp.PendSim`);
* `hEvStep_handler`, `evRun_handler`: labelled steps and runs lift through a handler;
* `wpl_append_normal`, `wpl_append_abruptP`: sequences;
* `CoreLQ`, `CoreLP`, `CoreLT`: `CoreGoodQ` with the host events `q`, for any postcondition, for
  `MatchP r`, and for a trap in any store and frame (`TrapPost`). The cases are in `Cases`,
  `Calls` and `TrapCases`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallX (tailPop TailRes tailFlow)
open Silmaril.Wasm.Abstract.CallXT (typeArity tailAnn)
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- The empty host: host-free steps. -/
abbrev NH : HostSemantics H := fun _ _ _ _ => False

/-! ## Logged runs to a final form -/

/-- **A logged Core run of `c` to a final form satisfying `Q`**, its host events `q`. -/
def WPL (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (c : Config H)
    (q : List (Call (wasmHostSig H))) (Q : Post H) : Prop :=
  ∃ (s' : Store H) (f' : Frame) (c' : List Admin) (o : Outcome),
    EvRun P host c q ⟨s', f', c'⟩ ∧ o.Ends c' ∧ Q s' f' o

section Basic

variable {c c₁ : Config H} {q q₁ q₂ : List (Call (wasmHostSig H))} {Q Q' : Post H}

theorem wpl_of_wp {s : Store H} {f : Frame} {code : List Admin} (h : WP P NH s f code Q) :
    WPL P host ⟨s, f, code⟩ [] Q := by
  obtain ⟨s', f', c', o, hs, he, hq⟩ := h
  exact ⟨s', f', c', o, evRun_of_free hs, he, hq⟩

theorem wpl_evRun (h₁ : EvRun P host c q₁ c₁) (h₂ : WPL P host c₁ q₂ Q) :
    WPL P host c (q₁ ++ q₂) Q := by
  obtain ⟨s', f', c', o, h, he, hq⟩ := h₂
  exact ⟨s', f', c', o, evRun_trans h₁ h, he, hq⟩

theorem wpl_free (hs : Steps P NH c c₁) (h : WPL P host c₁ q Q) : WPL P host c q Q := by
  simpa using wpl_evRun (evRun_of_free hs) h

theorem wpl_mono (h : WPL P host c q Q) (hQ : ∀ s f o, Q s f o → Q' s f o) : WPL P host c q Q' := by
  obtain ⟨s', f', c', o, hs, he, hq⟩ := h
  exact ⟨s', f', c', o, hs, he, hQ _ _ _ hq⟩

/-- **The logged run of a hole in a context**: a context lifting every labelled step lifts the
hole's logged run; a host-free exit from the context around the hole's final form ends the
outer run. -/
theorem wpl_wrap (W : Config H → Config H)
    (hW : ∀ c l c', HEvStep P host c l c' → HEvStep P host (W c) l (W c'))
    (h : WPL P host c q Q)
    (hx : ∀ s' f' c' o, o.Ends c' → Q s' f' o →
      WP P NH (W ⟨s', f', c'⟩).store (W ⟨s', f', c'⟩).frame (W ⟨s', f', c'⟩).code Q') :
    WPL P host (W c) q Q' := by
  obtain ⟨s', f', c', o, hs, he, hq⟩ := h
  have h₁ := evRun_wrap W hW hs
  have h₂ := wpl_of_wp (host := host) (hx s' f' c' o he hq)
  simpa using wpl_evRun h₁ h₂

/-- **The logged run of a hole in a context, then a logged exit**: as `wpl_wrap`, the context
around the hole's final form going on with a logged run. -/
theorem wpl_wrapK (W : Config H → Config H)
    (hW : ∀ c l c', HEvStep P host c l c' → HEvStep P host (W c) l (W c'))
    (h : WPL P host c q₁ Q)
    (hx : ∀ s' f' c' o, o.Ends c' → Q s' f' o → WPL P host (W ⟨s', f', c'⟩) q₂ Q') :
    WPL P host (W c) (q₁ ++ q₂) Q' := by
  obtain ⟨s', f', c', o, hs, he, hq⟩ := h
  exact wpl_evRun (evRun_wrap W hW hs) (hx s' f' c' o he hq)

end Basic

/-! ## Contexts -/

theorem decompose?_handler_some {s : Store H} {n : Nat} {cs : List Catch} {b : List Admin}
    {E : SingleThreaded.Ctx} {a : Nat} {hh : H} {us : List Val}
    (hd : SingleThreaded.decompose? s b = some (E, a, hh, us)) :
    SingleThreaded.decompose? s [.handler n cs b] = some (.handler [] n cs E [], a, hh, us) := by
  have hs : SingleThreaded.splitVals [Admin.handler n cs b] = ([], [.handler n cs b]) := by
    simp [SingleThreaded.splitVals, Admin.val?]
  rw [SingleThreaded.decompose?_of_split hs, SingleThreaded.decompHead_handler, hd]
  rfl

/-- **A labelled step lifts through a handler**, with the same label. -/
theorem hEvStep_handler {s s' : Store H} {f f' : Frame} {b b' : List Admin}
    {l : Option (Call (wasmHostSig H))} (n : Nat) (cs : List Catch)
    (h : HEvStep P host ⟨s, f, b⟩ l ⟨s', f', b'⟩) :
    HEvStep P host ⟨s, f, [.handler n cs b]⟩ l ⟨s', f', [.handler n cs b']⟩ := by
  cases l with
  | none =>
    rcases h with h | ⟨hc, E, a, hh, us, hd, hdiv⟩
    · exact .inl (Step.ctxtHandler h)
    · simp only [Config.mk.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      exact .inr ⟨rfl, _, a, hh, us, decompose?_handler_some hd, hdiv⟩
  | some e =>
    obtain ⟨E, a, hd, hs, hans, hc⟩ := h
    simp only [Config.mk.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact ⟨_, a, decompose?_handler_some hd, hs, hans, by simp [SingleThreaded.Ctx.fill, vals]⟩

/-- A labelled run inside a handler. -/
theorem evRun_handler {s s' : Store H} {f f' : Frame} {es es' : List Admin}
    {q : List (Call (wasmHostSig H))} (n : Nat) (cs : List Catch)
    (h : EvRun P host ⟨s, f, es⟩ q ⟨s', f', es'⟩) :
    EvRun P host ⟨s, f, [.handler n cs es]⟩ q ⟨s', f', [.handler n cs es']⟩ :=
  evRun_wrap (fun c => ⟨c.store, c.frame, [.handler n cs c.code]⟩)
    (fun ⟨_, _, _⟩ _ ⟨_, _, _⟩ h => hEvStep_handler n cs h) h

/-- The sequence context `vals pre ++ · ++ rest`. -/
abbrev Wseq (pre : List Val) (rest : List Admin) (c : Config H) : Config H :=
  ⟨c.store, c.frame, vals pre ++ c.code ++ rest⟩

/-- A label in a sequence context. -/
abbrev Wlab (pre : List Val) (rest : List Admin) (n : Nat) (cont : List Instr) (c : Config H) :
    Config H :=
  ⟨c.store, c.frame, vals pre ++ [.label n cont c.code] ++ rest⟩

/-- A `try_table`'s handler and label in a sequence context. -/
abbrev Wtry (pre : List Val) (rest : List Admin) (n : Nat) (cs : List Catch) (c : Config H) :
    Config H :=
  ⟨c.store, c.frame, vals pre ++ [.handler n cs [.label n [] c.code]] ++ rest⟩

/-- A callee's frame and label, in the caller's frame `f`. -/
abbrev Wfr (n : Nat) (f : Frame) (c : Config H) : Config H :=
  ⟨c.store, f, [.frame n c.frame [.label n [] c.code]]⟩

theorem hW_seq (pre : List Val) (rest : List Admin) :
    ∀ (c : Config H) l c', HEvStep P host c l c' → HEvStep P host (Wseq pre rest c) l
      (Wseq pre rest c') :=
  fun ⟨_, _, _⟩ _ ⟨_, _, _⟩ h => hEvStep_ctx pre rest h

theorem hW_lab (pre : List Val) (rest : List Admin) (n : Nat) (cont : List Instr) :
    ∀ (c : Config H) l c', HEvStep P host c l c' → HEvStep P host (Wlab pre rest n cont c) l
      (Wlab pre rest n cont c') :=
  fun ⟨_, _, _⟩ _ ⟨_, _, _⟩ h => hEvStep_ctx pre rest (hEvStep_label n cont h)

theorem hW_try (pre : List Val) (rest : List Admin) (n : Nat) (cs : List Catch) :
    ∀ (c : Config H) l c', HEvStep P host c l c' → HEvStep P host (Wtry pre rest n cs c) l
      (Wtry pre rest n cs c') :=
  fun ⟨_, _, _⟩ _ ⟨_, _, _⟩ h => hEvStep_ctx pre rest (hEvStep_handler n cs (hEvStep_label n [] h))

theorem hW_fr (n : Nat) (f : Frame) :
    ∀ (c : Config H) l c', HEvStep P host c l c' → HEvStep P host (Wfr n f c) l (Wfr n f c') :=
  fun ⟨_, _, _⟩ _ ⟨_, _, _⟩ h => hEvStep_frame n (hEvStep_label n [] h)

/-! ## `MatchP` final forms -/

section Final

variable {s s₁ : Store H} {f f₁ : Frame} {c : List Admin} {q q₁ q₂ : List (Call (wasmHostSig H))}
  {Q : Post H}

/-- A final form satisfying `Q`, in one step-free run. -/
theorem wp_final {c' : List Admin} {o : Outcome} (he : o.Ends c') (hq : Q s f o) :
    WP P NH s f c' Q :=
  ⟨s, f, c', o, .refl, he, hq⟩

/-- **A sequence whose first part completes normally.** -/
theorem wpl_append_normal {stk₁ : List Val} {rest : List Admin}
    (h : WPL P host ⟨s, f, c⟩ q₁ (MatchP (s₁, f₁, .flow (.normal stk₁))))
    (hk : WPL P host ⟨s₁, f₁, vals stk₁.reverse ++ rest⟩ q₂ Q) :
    WPL P host ⟨s, f, c ++ rest⟩ (q₁ ++ q₂) Q := by
  obtain ⟨s', f', c', o, hrun, he, hm⟩ := h
  rcases matchP_flow_iff.mp hm with ⟨rfl, rfl, hm⟩ | ⟨h, -⟩
  · have hc : c' = vals stk₁.reverse := ends_normal hm he
    subst hc
    have h₁ := evRun_wrap (Wseq [] rest) (hW_seq [] rest) hrun
    simp only [Wseq, vals, List.map_nil, List.nil_append] at h₁
    exact wpl_evRun h₁ hk
  · cases h

/-- **A sequence whose first part ends abruptly.** -/
theorem wpl_append_abruptP {rest : List Admin} {o : POut}
    (h : WPL P host ⟨s, f, c⟩ q (MatchP (s₁, f₁, o))) (hn : ¬ o.IsNormal) :
    WPL P host ⟨s, f, c ++ rest⟩ q (MatchP (s₁, f₁, o)) := by
  have := wpl_wrap (Wseq [] rest) (hW_seq [] rest) h fun s' f' c' o' he hq =>
    by simpa using wp_append_abruptP (P := P) (host := NH) (rest := rest) (wp_final he hq) hn
  simpa [Wseq, vals] using this

/-- `MatchP` of a flow from `Match`. -/
theorem wpl_matchP {fl : Binaryen.Flow} {code : List Admin}
    (h : WPL P host ⟨s, f, code⟩ q (Match (s₁, f₁, fl))) :
    WPL P host ⟨s, f, code⟩ q (MatchP (s₁, f₁, .flow fl)) :=
  wpl_mono h fun _ _ _ hm => .inl hm

end Final

/-! ## The logged Core invariant -/

/-- **The logged Core-run invariant, any postcondition**: from checked code on a checked store,
a logged Core run with the host events `q` to a final form satisfying `Q`. -/
def CoreLQ (tags : List TagInst) (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (stk : List Val) (es : List Binaryen.BExpr) (Q : Post H)
    (q : List (Call (wasmHostSig H))) : Prop :=
  ∀ {labels : List Nat} {ret : Nat} {out : Option Nat}, StoreChkE (ehExt tags) s.funcs →
    chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length) es = some out →
    WPL P host ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ q Q

/-- **The logged Core-run invariant with pending tail calls**: `CoreGoodP (ehExt tags)` with the
host events `q`. -/
abbrev CoreLP (tags : List TagInst) (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (stk : List Val) (es : List Binaryen.BExpr)
    (r : Store H × Frame × POut) (q : List (Call (wasmHostSig H))) : Prop :=
  CoreLQ tags P host s f stk es (MatchP r) q

/-- **A trap**, in any store and frame: the postcondition of a run cut at a trapping callee. -/
def TrapPost : Post H := fun _ _ o => o = .trap

/-- The logged Core-run invariant of a run cut at a trapping callee. -/
abbrev CoreLT (tags : List TagInst) (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (stk : List Val) (es : List Binaryen.BExpr)
    (q : List (Call (wasmHostSig H))) : Prop :=
  CoreLQ tags P host s f stk es TrapPost q

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
