module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.PendClose
public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.BackWhole

/-!
# Pending calls of the canonical closure are Core runs at exactly their log (proofs)

A Core run to a host call is read through the trapping behaviours of #548's simulations, at a
host that also answers that call by a trap:

* `answerAt host m`: `host`, also answering the host call `m` by a trap in its store. It keeps
  every hypothesis of the forward and backward simulations (`nativeHostSlice_answerAt`,
  `hostSliceE_answerAt`, `hostTyped_answerAt`), and its runs with a log `host` allows are runs of
  `host` (`evRun_of_answerAt`);
* `wasmEvPendXP_evRun` (every profile): a pending call `(cs, m)` answered by a trap is a trapping
  behaviour of the closure (`pendLXP_trap`), so a Core run of `answerAt host m` to a trap with the
  log `cs ++ [trapEv m]` (`wasmEvFunXP_trap_evRun`); cut at its last event (`evRun_split`), the
  run reaches the host call `m` with exactly the log `cs`;
* `evRun_pendXP` (deterministic profile): a Core run with the log `cs` to a host call `m`, the
  call answered by a trap (`answerAt`), the trap leaving every context (`fill_trap_steps'`), is a
  Core run to a trap with the log `cs ++ [trapEv m]`, so a trapping behaviour of the closure
  (`evRun_wasmEvFunXP_trap`), whose log before its last event is a pending call (`close_pend`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Interp
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-! ## A host answering one call by a trap -/

/-- `host`, also answering the host call `m` by a trap in its store. -/
def answerAt (host : HostSemantics H) (m : (wasmHostSig H).Op) : HostSemantics H :=
  fun h s vs o =>
    host h s vs o ∨ (h = m.1 ∧ s = m.2.1 ∧ vs = m.2.2 ∧ o = .returned m.2.1 .trap)

theorem nativeHostSlice_answerAt (hH : NativeHostSlice host) (m : (wasmHostSig H).Op) :
    NativeHostSlice (answerAt host m) where
  funcs h s vs s' r hr := by
    rcases hr with hr | ⟨-, rfl, -, he⟩
    · exact hH.funcs h s vs s' r hr
    · cases he; exact FuncsGood.refl _
  arity s a fi h ps rs vs ws s' hf hc hty hr := by
    rcases hr with hr | ⟨-, -, -, he⟩
    · exact hH.arity s a fi h ps rs vs ws s' hf hc hty hr
    · cases he
  noThrow h s vs s' t hr := by
    rcases hr with hr | ⟨-, -, -, he⟩
    · exact hH.noThrow h s vs s' t hr
    · cases he

theorem hostSliceE_answerAt {tags : List TagInst} (hE : HostSliceE tags host)
    (m : (wasmHostSig H).Op) : HostSliceE tags (answerAt host m) where
  chk h s vs s' r hr := by
    rcases hr with hr | ⟨-, rfl, -, he⟩
    · exact hE.chk h s vs s' r hr
    · cases he; exact id
  tags h s vs s' r hr := by
    rcases hr with hr | ⟨-, rfl, -, he⟩
    · exact hE.tags h s vs s' r hr
    · cases he; exact id

theorem hostTyped_answerAt (hT : HostTyped host) (m : (wasmHostSig H).Op) :
    HostTyped (answerAt host m) := by
  intro s fi h vs ps rs hs hfi hcode he hvs out hout
  rcases hout with hout | ⟨-, rfl, -, rfl⟩
  · exact hT s fi h vs ps rs hs hfi hcode he hvs out hout
  · exact ⟨hs, Extend.refl hs, trivial⟩

theorem cons_answerAt {m : (wasmHostSig H).Op} {q : List (Call (wasmHostSig H))}
    (hc : Cons host q) : Cons (answerAt host m) (q ++ [trapEv m]) := by
  intro e he
  rcases List.mem_append.1 he with he | he
  · exact Or.inl (hc e he)
  · rw [List.mem_singleton] at he
    subst he
    exact Or.inr ⟨rfl, rfl, rfl, rfl⟩

/-- **Runs of `answerAt host m` with a log `host` allows are runs of `host`.** -/
theorem evRun_of_answerAt {m : (wasmHostSig H).Op} {c c' : Config H}
    {cs : List (Call (wasmHostSig H))} (h : EvRun P (answerAt host m) c cs c') :
    Cons host cs → EvRun P host c cs c' := by
  induction h with
  | refl => exact fun _ => .refl _
  | silent hs _ ih =>
    intro hc
    rcases hs with hs | ⟨rfl, E, a, hh, us, hd, hdiv⟩
    · exact .silent (.inl hs) (ih hc)
    · rcases hdiv with hdiv | ⟨-, -, -, he⟩
      · exact .silent (.inr ⟨rfl, E, a, hh, us, hd, hdiv⟩) (ih hc)
      · cases he
  | @event c₁ c₂ c₃ e cs hs _ ih =>
    intro hc
    obtain ⟨E, a, hdec, hst, -, hc'⟩ := hs
    have he : host e.1.1 e.1.2.1 e.1.2.2 (.returned e.2.1 e.2.2) := hc e List.mem_cons_self
    rw [hst] at he
    exact .event ⟨E, a, hdec, hst, he, hc'⟩
      (ih fun x hx => hc x (List.mem_cons_of_mem _ hx))

/-- **Runs of `host` are runs of `answerAt host m`.** -/
theorem evRun_answerAt {m : (wasmHostSig H).Op} {c c' : Config H}
    {cs : List (Call (wasmHostSig H))} (h : EvRun P host c cs c') :
    EvRun P (answerAt host m) c cs c' := by
  induction h with
  | refl => exact .refl _
  | silent hs _ ih =>
    rcases hs with hs | ⟨rfl, E, a, hh, us, hd, hdiv⟩
    · exact .silent (.inl hs) ih
    · exact .silent (.inr ⟨rfl, E, a, hh, us, hd, .inl hdiv⟩) ih
  | event hs _ ih =>
    obtain ⟨E, a, hdec, hst, he, hc'⟩ := hs
    exact .event ⟨E, a, hdec, hst, .inl he, hc'⟩ ih

/-! ## Runs cut at an event; traps -/

/-- **A labelled run cut at one of its events.** -/
theorem evRun_split {c c' : Config H} {l : List (Call (wasmHostSig H))}
    (h : EvRun P host c l c') :
    ∀ (cs cs' : List (Call (wasmHostSig H))) (e : Call (wasmHostSig H)), l = cs ++ e :: cs' →
      ∃ c₁ c₂, EvRun P host c cs c₁ ∧ HEvStep P host c₁ (some e) c₂ ∧ EvRun P host c₂ cs' c' := by
  induction h with
  | refl => intro cs cs' e h; simp at h
  | silent hs _ ih =>
    intro cs cs' e h
    obtain ⟨c₁, c₂, r₁, st, r₂⟩ := ih cs cs' e h
    exact ⟨c₁, c₂, .silent hs r₁, st, r₂⟩
  | @event c₁ c₂ c₃ e₀ l hs hr ih =>
    intro cs cs' e h
    rcases cs with _ | ⟨x, cs⟩
    · simp only [List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨c₁, c₂, .refl _, hs, hr⟩
    · simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨d₁, d₂, r₁, st, r₂⟩ := ih cs cs' e h
      exact ⟨d₁, d₂, .event hs r₁, st, r₂⟩

/-- A trap in a callout context reaches the top, host-free, with the store unchanged. -/
theorem fill_trap_steps' (s : Store H) :
    ∀ (E : SingleThreaded.Ctx) (f : Frame), ∃ f', Steps P NH ⟨s, f, E.fill [.trap]⟩ ⟨s, f', [.trap]⟩ := by
  have top : ∀ (g : Frame) (pre : List Val) (rest : List Admin),
      Steps P NH ⟨s, g, vals pre ++ [.trap] ++ rest⟩ ⟨s, g, [.trap]⟩ := by
    intro g pre rest
    by_cases hne : pre ≠ [] ∨ rest ≠ []
    · exact .single (Step.trapInstrs hne)
    · simp only [ne_eq, not_or, not_not] at hne
      obtain ⟨rfl, rfl⟩ := hne
      simpa [vals] using (Relation.ReflTransGen.refl : Steps P NH ⟨s, g, [.trap]⟩ _)
  intro E
  induction E with
  | top pre rest => intro f; exact ⟨f, top f pre rest⟩
  | label pre n cont E rest ih =>
    intro f
    obtain ⟨f', h⟩ := ih f
    exact ⟨f', ((Steps.ctxtInstrs (vs := pre) (rest := rest) (Steps.label (n := n) (cont := cont) h)).trans
      (Steps.ctxtInstrs (Relation.ReflTransGen.single Step.trapLabel))).trans (top f' pre rest)⟩
  | handler pre n cs E rest ih =>
    intro f
    obtain ⟨f', h⟩ := ih f
    exact ⟨f', ((Steps.ctxtInstrs (vs := pre) (rest := rest) (Steps.handler (n := n) (cs := cs) h)).trans
      (Steps.ctxtInstrs (Relation.ReflTransGen.single Step.trapHandler))).trans (top f' pre rest)⟩
  | frame pre n fi E rest ih =>
    intro f
    obtain ⟨f', h⟩ := ih fi
    exact ⟨f, ((Steps.ctxtInstrs (vs := pre) (rest := rest) (Steps.frame (f := f) (n := n) h)).trans
      (Steps.ctxtInstrs (Relation.ReflTransGen.single Step.trapFrame))).trans (top f pre rest)⟩

/-- The type of an invoked function. -/
theorem invokeOk_type {s : Store H} {a : Nat} {vs : List Val} (hok : InvokeOk s a vs) :
    ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), s.funcs[a]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) := by
  obtain ⟨fi, ps, rs, hfi, he, -⟩ := id hok
  refine ⟨fi, ps.toList, rs.toList, hfi, ?_⟩
  unfold Validation.DefType.funcType?
  rw [Validation.Expand.iff.mp he]

/-! ## Pending calls -/

/-- **Pending calls, natively to Core, at exactly their log** (every profile). -/
theorem wasmEvPendXP_evRun {tags : List TagInst} (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s : Store H} {a : Nat} {vs : List Val} (hts : TagsOk tags s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op}
    (h : (cs, m) ∈ wasmEvPendXP s (a, vs)) (hc : Cons host cs) :
    ∃ (c : Config H) (E : SingleThreaded.Ctx) (a' : Nat), EvRun P host (invoke s a vs) cs c ∧
      SingleThreaded.decompose? c.store c.code = some (E, a', m.1, m.2.2) ∧ c.store = m.2.1 := by
  obtain ⟨fi, ps, rs, hfi, hty⟩ := invokeOk_type hok
  have hcl : (cs ++ [trapEv m], .trap) ∈ wasmEvFunXP s (a, vs) := pendLXP_trap h hfi hty
  obtain ⟨s₂, run⟩ := wasmEvFunXP_trap_evRun (P := P) (nativeHostSlice_answerAt hH m)
    (hostSliceE_answerAt hE m) hts hS hok hcl (cons_answerAt hc)
  obtain ⟨c₁, c₂, r₁, st, -⟩ := evRun_split run cs [] (trapEv m) rfl
  obtain ⟨E, a', hd, hst, -, -⟩ := st
  exact ⟨c₁, E, a', evRun_of_answerAt r₁ hc, hd, hst.symm⟩

/-- **Core runs to a host call are pending calls at exactly their log** (deterministic
profile). -/
theorem evRun_pendXP {o : GrowOracle} {tags : List TagInst} (hT : HostTyped host)
    (hH : NativeHostSlice host) (hE : HostSliceE tags host) {s : Store H} {a : Nat}
    {vs : List Val} (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s)
    (hok : InvokeOk s a vs) {c : Config H} {cs : List (Call (wasmHostSig H))}
    {E : SingleThreaded.Ctx} {a' : Nat} {hh : H} {us : List Val}
    (hrun : EvRun (profile o) host (invoke s a vs) cs c)
    (hd : SingleThreaded.decompose? c.store c.code = some (E, a', hh, us)) :
    (cs, (hh, c.store, us)) ∈ wasmEvPendXP s (a, vs) := by
  let m : (wasmHostSig H).Op := (hh, c.store, us)
  have st : HEvStep (profile o) (answerAt host m) c (some (trapEv m))
      ⟨c.store, c.frame, E.fill [.trap]⟩ :=
    ⟨E, a', hd, rfl, Or.inr ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
  obtain ⟨f', ht⟩ := fill_trap_steps' (P := profile o) c.store E c.frame
  have run := evRun_trans (evRun_answerAt (m := m) hrun) (.event st (evRun_of_free ht))
  have hcl := evRun_wasmEvFunXP_trap (hostTyped_answerAt hT m) (nativeHostSlice_answerAt hH m)
    (hostSliceE_answerAt hE m) hs hS hts hok run
  exact close_pend (w := []) hcl

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
