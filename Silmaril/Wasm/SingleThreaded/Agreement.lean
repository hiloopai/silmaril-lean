module

public import Silmaril.Wasm.SingleThreaded.Thread
public import Silmaril.Wasm.SingleThreaded.NoRedex
public import Silmaril.Wasm.Execution.Core.Properties

@[expose] public section

/-! # Agreement of the single-threaded presentation with Core reduction (U26)

A Core step of a thread's configuration, in the single-threaded profile and with
an arbitrary host relation, is exactly one of:

* an internal step (`Internal`, host-free); or
* the thread is at a callout `h args`, and the host either returns `(s', r)` —
  the step lands in `resumeResult s t r` over `s'` — or diverges (a stutter).
-/

namespace Silmaril.Wasm.SingleThreaded

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- Internal steps are exactly host-free Core steps landing in active threads. -/
theorem internal_iff (o : GrowOracle) (s s' : Store H) (t : Thread) (f' : Frame)
    (code' : List Admin) :
    Internal o (s, t) (s', .active f' code') ↔
      Step (profile o) (fun _ _ _ _ => False) (t.config s) ⟨s', f', code'⟩ := by
  constructor
  · rintro ⟨f'', code'', heq, h⟩
    cases heq
    exact h
  · intro h
    exact ⟨f', code', rfl, h⟩

/-! ## Helpers: host-call redexes under contexts -/

theorem Thread.config_store (s : Store H) (t : Thread) : (t.config s).store = s := by
  cases t <;> rfl

theorem Thread.config_eta (s : Store H) (t : Thread) :
    t.config s = ⟨s, (t.config s).frame, (t.config s).code⟩ := by
  cases t <;> rfl

theorem topRedex_wrap {s : Store H} {ws : List Val} {r : List Admin} {E : Ctx} {a : Nat} {h : H}
    {args : List Val} (vs : List Val) (rest : List Admin)
    (ht : topRedex s ws r = some (E, a, h, args)) :
    topRedex s (vs ++ ws) (r ++ rest) = some (E.wrap vs rest, a, h, args) := by
  unfold topRedex at ht ⊢
  split at ht
  · rename_i a' hl
    split at ht
    · rename_i h' n hh
      dsimp only at ht
      split at ht
      · rename_i hn
        simp only [Option.some.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
        obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hl
        simp only [List.dropLast_concat] at hn ⊢
        rw [← List.append_assoc]
        simp only [List.getLast?_concat, List.dropLast_concat, hh, List.length_append]
        rw [ite_eq_left (by omega)]
        simp only [Ctx.wrap, Option.some.injEq, Prod.mk.injEq]
        have hk : vs.length + ys.length - n = vs.length + (ys.length - n) := by omega
        rw [hk, List.take_length_add_append, List.drop_length_add_append]
        simp
      · cases ht
    · cases ht
  · cases ht

theorem decompose?_wrap {s : Store H} {is : List Admin} {E : Ctx} {a : Nat} {h : H}
    {args : List Val} (vs : List Val) (rest : List Admin)
    (hd : decompose? s is = some (E, a, h, args)) :
    decompose? s (vals vs ++ is ++ rest) = some (E.wrap vs rest, a, h, args) := by
  rcases hsp : splitVals is with ⟨ws, _ | ⟨d, r⟩⟩
  · rw [decompose?_of_split_nil hsp] at hd; cases hd
  · obtain ⟨hcode, hdv⟩ := splitVals_eq hsp
    have hw : splitVals (vals vs ++ is ++ rest) = (vs ++ ws, d :: (r ++ rest)) := by
      rw [hcode, ← splitVals_vals_cons hdv]; simp
    rw [decompose?_of_split hw]
    rw [decompose?_of_split hsp] at hd
    cases d with
    | label n cont body =>
      simp only [decompHead, Option.map_eq_some_iff] at hd ⊢
      obtain ⟨x, hb, heq⟩ := hd
      refine ⟨x, hb, ?_⟩
      simp only [Prod.mk.injEq] at heq ⊢
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
      exact ⟨rfl, rfl, rfl, rfl⟩
    | handler n cs body =>
      simp only [decompHead, Option.map_eq_some_iff] at hd ⊢
      obtain ⟨x, hb, heq⟩ := hd
      refine ⟨x, hb, ?_⟩
      simp only [Prod.mk.injEq] at heq ⊢
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
      exact ⟨rfl, rfl, rfl, rfl⟩
    | frame n f body =>
      simp only [decompHead, Option.map_eq_some_iff] at hd ⊢
      obtain ⟨x, hb, heq⟩ := hd
      refine ⟨x, hb, ?_⟩
      simp only [Prod.mk.injEq] at heq ⊢
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
      exact ⟨rfl, rfl, rfl, rfl⟩
    | _ =>
      simp only [decompHead] at hd ⊢
      split at hd
      · rw [ite_eq_left (by assumption)]; exact topRedex_wrap vs rest hd
      · cases hd

theorem decompose?_redex {s : Store H} {vs : List Val} {a : Nat} {c : Admin} {fi : FuncInst H}
    {ps rs : Ty (.list .val)} {h : H} (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : vs.length = ps.length) (hcode : fi.code = .host h) :
    decompose? s (vals vs ++ [.ref (.func a), c]) = some (.top [] [], a, h, vs) := by
  have hw : splitVals (vals vs ++ [.ref (.func a), c]) = (vs ++ [.ref (.func a)], [c]) := by
    rw [show vals vs ++ [.ref (.func a), c] = vals (vs ++ [.ref (.func a)]) ++ c :: [] by
      simp; rfl, splitVals_vals_cons (Admin.val?_of_IsCallRef hc)]
  rw [decompose?_of_split hw, decompHead_of_IsCallRef hc]
  unfold topRedex
  simp [hostArity?_of hf hcode he, hn]

/-- Lifting a frame-independent step through a callout context. -/
theorem Ctx.step_fill {P : Profile} {host : HostSemantics H} (E : Ctx) {s s' : Store H}
    {xs ys : List Admin} (hstep : ∀ g : Frame, Step P host ⟨s, g, xs⟩ ⟨s', g, ys⟩) (f : Frame) :
    Step P host ⟨s, f, E.fill xs⟩ ⟨s', f, E.fill ys⟩ := by
  have lift : ∀ {g g' : Frame} {pre : List Val} {is is' rest : List Admin},
      Step P host ⟨s, g, is⟩ ⟨s', g', is'⟩ →
      Step P host ⟨s, g, vals pre ++ is ++ rest⟩ ⟨s', g', vals pre ++ is' ++ rest⟩ := by
    intro g g' pre is is' rest h
    by_cases hne : pre ≠ [] ∨ rest ≠ []
    · exact Step.ctxtInstrs h hne
    · simp only [ne_eq, not_or, not_not] at hne
      obtain ⟨rfl, rfl⟩ := hne
      simpa [vals] using h
  induction E generalizing f with
  | top pre rest => exact lift (hstep f)
  | label pre n cont E rest ih =>
    exact lift (is := [_]) (Step.ctxtLabel (ih f))
  | handler pre n cs E rest ih =>
    exact lift (is := [_]) (Step.ctxtHandler (ih f))
  | frame pre n fi E rest ih =>
    exact lift (is := [_]) (Step.ctxtFrame (ih fi))

/-- A Core step either is host-free or is a host call at the `decompose?` redex. -/
theorem Step.split_host {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') :
    Step P (fun _ _ _ _ => False) c c' ∨
      ∃ E a hh args, decompose? c.store c.code = some (E, a, hh, args) ∧
        ((∃ s' r, host hh c.store args (.returned s' r) ∧ c' = ⟨s', c.frame, E.fill r.toAdmin⟩) ∨
          (host hh c.store args .diverged ∧ c' = c)) := by
  induction h with
  | parametric h => exact Or.inl (.parametric h)
  | numeric h => exact Or.inl (.numeric h)
  | vector h => exact Or.inl (.vector h)
  | «variable» h => exact Or.inl (.«variable» h)
  | table h => exact Or.inl (.table h)
  | memory h => exact Or.inl (.memory h)
  | reference h => exact Or.inl (.reference h)
  | aggregate h => exact Or.inl (.aggregate h)
  | @ctxtInstrs s s' f f' vs is is' rest _ hne ih =>
    rcases ih with ih | ⟨E, a, hh, args, hd, ⟨s'', r, hr, heq⟩ | ⟨hdiv, heq⟩⟩
    · exact Or.inl (.ctxtInstrs ih hne)
    · simp only [Config.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact Or.inr ⟨E.wrap vs rest, a, hh, args, decompose?_wrap vs rest hd,
        Or.inl ⟨_, r, hr, by simp [Ctx.fill_wrap]⟩⟩
    · simp only [Config.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact Or.inr ⟨E.wrap vs rest, a, hh, args, decompose?_wrap vs rest hd, Or.inr ⟨hdiv, rfl⟩⟩
  | @ctxtLabel s s' f f' n cont is is' _ ih =>
    rcases ih with ih | ⟨E, a, hh, args, hd, ⟨s'', r, hr, heq⟩ | ⟨hdiv, heq⟩⟩
    · exact Or.inl (.ctxtLabel ih)
    · simp only [Config.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      refine Or.inr ⟨.label [] n cont E [], a, hh, args, ?_, Or.inl ⟨_, r, hr, by simp [Ctx.fill]⟩⟩
      rw [decompose?_eq]; simp [splitVals, Admin.val?, decompTop, decompHead, hd]
    · simp only [Config.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      refine Or.inr ⟨.label [] n cont E [], a, hh, args, ?_, Or.inr ⟨hdiv, rfl⟩⟩
      rw [decompose?_eq]; simp [splitVals, Admin.val?, decompTop, decompHead, hd]
  | @ctxtHandler s s' f f' n cs is is' _ ih =>
    rcases ih with ih | ⟨E, a, hh, args, hd, ⟨s'', r, hr, heq⟩ | ⟨hdiv, heq⟩⟩
    · exact Or.inl (.ctxtHandler ih)
    · simp only [Config.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      refine Or.inr ⟨.handler [] n cs E [], a, hh, args, ?_, Or.inl ⟨_, r, hr, by simp [Ctx.fill]⟩⟩
      rw [decompose?_eq]; simp [splitVals, Admin.val?, decompTop, decompHead, hd]
    · simp only [Config.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      refine Or.inr ⟨.handler [] n cs E [], a, hh, args, ?_, Or.inr ⟨hdiv, rfl⟩⟩
      rw [decompose?_eq]; simp [splitVals, Admin.val?, decompTop, decompHead, hd]
  | @ctxtFrame s s' f fi fi' n is is' _ ih =>
    rcases ih with ih | ⟨E, a, hh, args, hd, ⟨s'', r, hr, heq⟩ | ⟨hdiv, heq⟩⟩
    · exact Or.inl (.ctxtFrame ih)
    · simp only [Config.mk.injEq] at heq
      obtain ⟨h1, h2, h3⟩ := heq
      subst h1 h2 h3
      refine Or.inr ⟨.frame [] n fi' E [], a, hh, args, ?_, Or.inl ⟨_, r, hr, by simp [Ctx.fill]⟩⟩
      rw [decompose?_eq]; simp [splitVals, Admin.val?, decompTop, decompHead, hd]
    · simp only [Config.mk.injEq] at heq
      obtain ⟨h1, h2, h3⟩ := heq
      subst h1 h2 h3
      refine Or.inr ⟨.frame [] n fi' E [], a, hh, args, ?_, Or.inr ⟨hdiv, rfl⟩⟩
      rw [decompose?_eq]; simp [splitVals, Admin.val?, decompTop, decompHead, hd]
  | callRefHost hc hf he hn hcode hhost =>
    exact Or.inr ⟨_, _, _, _, decompose?_redex hc hf he hn hcode,
      Or.inl ⟨_, _, hhost, by simp [Ctx.fill]⟩⟩
  | callRefHostDiv hc hf he hn hcode hhost =>
    exact Or.inr ⟨_, _, _, _, decompose?_redex hc hf he hn hcode, Or.inr ⟨hhost, rfl⟩⟩
  | block hbt hm => exact Or.inl (.block hbt hm)
  | loop hbt hm => exact Or.inl (.loop hbt hm)
  | ifTrue hc => exact Or.inl (.ifTrue hc)
  | ifFalse => exact Or.inl .ifFalse
  | labelVals => exact Or.inl .labelVals
  | brLabelZero hl hn => exact Or.inl (.brLabelZero hl hn)
  | brLabelSucc hl => exact Or.inl (.brLabelSucc hl)
  | brHandler => exact Or.inl .brHandler
  | brIfTrue hc => exact Or.inl (.brIfTrue hc)
  | brIfFalse => exact Or.inl .brIfFalse
  | brTableLt hi => exact Or.inl (.brTableLt hi)
  | brTableGe hi => exact Or.inl (.brTableGe hi)
  | brOnNullNull => exact Or.inl .brOnNullNull
  | brOnNullAddr hv => exact Or.inl (.brOnNullAddr hv)
  | brOnNonNullNull => exact Or.inl .brOnNonNullNull
  | brOnNonNullAddr hv => exact Or.inl (.brOnNonNullAddr hv)
  | brOnCastSucceed h => exact Or.inl (.brOnCastSucceed h)
  | brOnCastFail h => exact Or.inl (.brOnCastFail h)
  | brOnCastFailSucceed h => exact Or.inl (.brOnCastFailSucceed h)
  | brOnCastFailFail h => exact Or.inl (.brOnCastFailFail h)
  | call hx hf => exact Or.inl (.call hx hf)
  | callRefNull hc => exact Or.inl (.callRefNull hc)
  | callRefFunc hc hf he hn hcode => exact Or.inl (.callRefFunc hc hf he hn hcode)
  | returnCall hx hf => exact Or.inl (.returnCall hx hf)
  | returnCallRefLabel hc => exact Or.inl (.returnCallRefLabel hc)
  | returnCallRefHandler hc => exact Or.inl (.returnCallRefHandler hc)
  | returnCallRefFrameNull hc => exact Or.inl (.returnCallRefFrameNull hc)
  | returnCallRefFrameAddr hc hf he hn => exact Or.inl (.returnCallRefFrameAddr hc hf he hn)
  | callIndirect => exact Or.inl .callIndirect
  | returnCallIndirect => exact Or.inl .returnCallIndirect
  | frameVals hn => exact Or.inl (.frameVals hn)
  | returnFrame hn => exact Or.inl (.returnFrame hn)
  | returnLabel => exact Or.inl .returnLabel
  | returnHandler => exact Or.inl .returnHandler
  | throw ht he hn => exact Or.inl (.throw ht he hn)
  | throwRefNull => exact Or.inl .throwRefNull
  | throwRefInstrs hne => exact Or.inl (.throwRefInstrs hne)
  | throwRefLabel => exact Or.inl .throwRefLabel
  | throwRefFrame => exact Or.inl .throwRefFrame
  | throwRefHandlerEmpty => exact Or.inl .throwRefHandlerEmpty
  | throwRefHandlerCatch he ht => exact Or.inl (.throwRefHandlerCatch he ht)
  | throwRefHandlerCatchRef he ht => exact Or.inl (.throwRefHandlerCatchRef he ht)
  | throwRefHandlerCatchAll => exact Or.inl .throwRefHandlerCatchAll
  | throwRefHandlerCatchAllRef => exact Or.inl .throwRefHandlerCatchAllRef
  | throwRefHandlerNext h => exact Or.inl (.throwRefHandlerNext h)
  | tryTable hbt hm => exact Or.inl (.tryTable hbt hm)
  | handlerVals => exact Or.inl .handlerVals
  | trapInstrs hne => exact Or.inl (.trapInstrs hne)
  | trapLabel => exact Or.inl .trapLabel
  | trapHandler => exact Or.inl .trapHandler
  | trapFrame => exact Or.inl .trapFrame

theorem resumeResult_config {s s' : Store H} {t : Thread} {E : Ctx} {a : Nat} {h : H}
    {args : List Val} {r : Result} (hd : decompose? s (t.config s).code = some (E, a, h, args)) :
    (resumeResult s t r).config s' = ⟨s', (t.config s).frame, E.fill r.toAdmin⟩ := by
  unfold resumeResult
  simp only
  rw [hd]
  rfl

/-- **Milestone (agreement).** -/
theorem step_iff (o : GrowOracle) (host : HostSemantics H) (s : Store H) (t : Thread)
    (c' : Config H) :
    Step (profile o) host (t.config s) c' ↔
      (∃ s' f' code', c' = ⟨s', f', code'⟩ ∧ Internal o (s, t) (s', .active f' code')) ∨
      (∃ E a h args, decompose? s (t.config s).code = some (E, a, h, args) ∧
        ((∃ s' r, host h s args (.returned s' r) ∧ c' = (resumeResult s t r).config s') ∨
         (host h s args .diverged ∧ c' = t.config s))) := by
  constructor
  · intro hstep
    rcases Step.split_host hstep with h | ⟨E, a, hh, args, hd, ⟨s', r, hr, heq⟩ | ⟨hdiv, heq⟩⟩
    · obtain ⟨s', f', code'⟩ := c'
      exact Or.inl ⟨s', f', code', rfl, f', code', rfl, h⟩
    · rw [Thread.config_store] at hd hr
      refine Or.inr ⟨E, a, hh, args, hd, Or.inl ⟨s', r, hr, ?_⟩⟩
      rw [heq, resumeResult_config hd]
    · rw [Thread.config_store] at hd hdiv
      exact Or.inr ⟨E, a, hh, args, hd, Or.inr ⟨hdiv, heq⟩⟩
  · rintro (⟨s', f', code', rfl, hi⟩ | ⟨E, a, hh, args, hd, ⟨s', r, hr, rfl⟩ | ⟨hdiv, rfl⟩⟩)
    · exact Step.of_noHost host ((internal_iff o s s' t f' code').mp hi)
    · obtain ⟨fi, yy, ps, rs, hf, hc, hyy, he, hn, hcode⟩ := decompose?_sound hd
      have : (resumeResult s t r).config s' =
          ⟨s', (t.config s).frame, E.fill r.toAdmin⟩ := resumeResult_config hd
      rw [this, Thread.config_eta s t, hcode]
      exact E.step_fill (fun g => Step.callRefHost hyy hf he hn hc hr) _
    · obtain ⟨fi, yy, ps, rs, hf, hc, hyy, he, hn, hcode⟩ := decompose?_sound hd
      rw [Thread.config_eta s t, hcode]
      exact E.step_fill (fun g => Step.callRefHostDiv hyy hf he hn hc hdiv) _

/-- Host-free steps are Core steps for any host. -/
theorem Internal.step {o : GrowOracle} {host : HostSemantics H} {s s' : Store H} {t : Thread}
    {f' : Frame} {code' : List Admin} (h : Internal o (s, t) (s', .active f' code')) :
    Step (profile o) host (t.config s) ⟨s', f', code'⟩ :=
  Step.of_noHost host ((internal_iff o s s' t f' code').mp h)

/-- `Internal` as a relation on configurations, for any host (graft from design A). -/
theorem Internal.toStep (o : GrowOracle) (host : HostSemantics H) {x y : Store H × Thread}
    (h : Internal o x y) : Step (profile o) host (x.2.config x.1) (y.2.config y.1) := by
  rcases x with ⟨s, t⟩
  rcases y with ⟨s', t'⟩
  obtain ⟨f', code', rfl, h⟩ := h
  exact Step.of_noHost host h

/-- A thread at a callout does not step internally. -/
theorem callout_no_internal {o : GrowOracle} {s : Store H} {t : Thread} {h : H} {args : List Val}
    (hs : status o s t = .callout h args) : ∀ y, ¬ Internal o (s, t) y := by
  rintro ⟨s', t'⟩ ⟨f', code', -, hstep⟩
  have hn := decompose?_none_of_noRedex (Step.noRedex hstep)
  rw [Thread.config_store] at hn
  unfold status at hs
  simp only at hs
  rw [hn] at hs
  split_ifs at hs

/-- Returned and stuck threads do not step. -/
theorem returned_no_internal {o : GrowOracle} {s : Store H} {t : Thread} {r : CallResult}
    (hs : status o s t = .returned r) : ∀ y, ¬ Internal o (s, t) y := by
  rintro ⟨s', t'⟩ ⟨f', code', -, hstep⟩
  have hq := Step.not_quiet hstep
  unfold status at hs
  simp only at hs
  split_ifs at hs with h1 h2 h3
  · obtain ⟨vs, hvs⟩ := h1
    exact hq (by rw [hvs]; exact quiet_vals vs)
  · exact hq (by rw [h2]; exact quiet_trap)
  · obtain ⟨a, ha⟩ := h3
    exact hq (by rw [ha]; exact quiet_throwing a)
  · split at hs
    · cases hs
    · cases hs
  · split at hs
    · cases hs
    · cases hs

theorem stuck_no_internal {o : GrowOracle} {s : Store H} {t : Thread}
    (hs : status o s t = .stuck) : ∀ y, ¬ Internal o (s, t) y := by
  intro y hy
  unfold status at hs
  simp only at hs
  split_ifs at hs with h1 h2 h3 h4 <;> try cases hs
  · split at hs <;> cases hs
  · split at hs
    · cases hs
    · exact h4 ⟨y, hy⟩

end Silmaril.Wasm.SingleThreaded
