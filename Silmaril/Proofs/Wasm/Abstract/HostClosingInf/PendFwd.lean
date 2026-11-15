module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.Conv

/-!
# Pending calls, natively to Core, at exactly their log (proofs)

The converse of `evRun_pend`, every profile: a pending call `(cs, m)` of `wasmEvPend` whose log
the host allows is a Core run of the invocation with exactly the host events `cs`, to a
configuration at the host call `m` (`decompose?`), in the store of `m`.

* `answerAt host m`: `host`, also answering the call `m` by a trap. A pending call may have no
  host outcome, so the context a descent builds (`Lifts`) is read at the call through a step of
  `answerAt host m`: lifting it shows the call under the context (`decompose?`). Its runs with a
  log that `host` allows are runs of `host` (`evRun_of_answerAt`);
* `pendL_fwd`: by induction on `PendL`, a pending call is reached by a Core run with its log,
  from the call into the host call, inside the callee frames and labels entered on the way
  (`reachL_fwd`, as in `descends_fwd`); a host function invoked directly is the empty run;
* `wasmEvPend_evRun`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInf

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Interp
open Shape (SubstPre)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

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

theorem cons_answerAt {m : (wasmHostSig H).Op} {q : List (Call (wasmHostSig H))}
    (hc : Cons host q) : Cons (answerAt host m) q :=
  fun e he => Or.inl (hc e he)

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

/-- **A pending call is reached by a Core run with its log**, from the call into the host call
`m`, inside the callee frames and labels entered on the way. -/
theorem pendL_fwd (hH : NativeHostSlice host) {s : Store H} {a : Nat} {vs : List Val}
    {cs : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op} (h : PendL s a vs cs m) :
    Cons host cs → InvC (⟨a, (vs, s)⟩ : (wasmOShape H).self.Op) →
      ∀ g : Frame, ∃ (z : (wasmOShape H).self.Op) (F' : Frame) (V : Config H → Config H)
        (fi : FuncInst H), Lifts P host V ∧
        EvRun P host (callAt ⟨a, (vs, s)⟩ g) cs (V (callAt z F')) ∧ InvC z ∧
        z.2.2.funcs[z.1]? = some fi ∧ fi.code = .host m.1 ∧ z.2.2 = m.2.1 ∧ z.2.1 = m.2.2 := by
  induction h with
  | @self s a vs fi hh hf hcode =>
    intro _ hx g
    exact ⟨⟨a, (vs, s)⟩, g, fun c => c, fi, lifts_id, .refl _, hx, hf, hcode, rfl, rfl⟩
  | @desc s a vs fi fn l q q' y m hf hcode hr hq _ ih =>
    intro hc hx g
    rw [cons_append] at hc
    obtain ⟨fi', ps, rs, hf', hty, hn, hS⟩ := hx
    obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans hf)
    obtain ⟨ob, hbc⟩ := body_chk hS hf hcode hty hn
    obtain ⟨hy, W, F', hW, run⟩ := reachL_fwd (P := P) hH hr q hq hc.1 hS hbc
    obtain ⟨z, F'', V, fz, hV, run', hz, hfz⟩ := ih hc.2 hy F'
    have hD := lifts_comp (lifts_frame (P := P) (host := host) rs.length g)
      (lifts_comp (lifts_label (P := P) (host := host) rs.length []) hW)
    refine ⟨z, F'', _, fz, lifts_comp hD hV, ?_, hz, hfz⟩
    have r1 := evRun_trans (evRun_of_free (enter_body (P := P) hf hcode hty hn g))
      (evRun_wrap _ (lifts_frame (P := P) (host := host) rs.length g)
        (evRun_wrap _ (lifts_label (P := P) (host := host) rs.length []) run))
    exact evRun_trans r1 (evRun_wrap _ hD run')

/-- **Pending calls, natively to Core, at exactly their log** (every profile, checked stores,
typed invocations, a host in the native host slice). -/
theorem wasmEvPend_evRun (hH : NativeHostSlice host) {s : Store H} {a : Nat} {vs : List Val}
    (hS : StoreChk s.funcs) (hok : InvokeOk s a vs) {cs : List (Call (wasmHostSig H))}
    {m : (wasmHostSig H).Op} (h : (cs, m) ∈ wasmEvPend s (a, vs)) (hc : Cons host cs) :
    ∃ (c : Config H) (E : SingleThreaded.Ctx) (a' : Nat), EvRun P host (invoke s a vs) cs c ∧
      SingleThreaded.decompose? c.store c.code = some (E, a', m.1, m.2.2) ∧ c.store = m.2.1 := by
  obtain ⟨z, F', V, fi, hV, run, hz, hf, hcode, hzs, hzu⟩ :=
    pendL_fwd (P := P) (host := answerAt host m) (nativeHostSlice_answerAt hH m) h
      (cons_answerAt hc) (invC_of_invokeOk hS hok) {}
  obtain ⟨fi', ps, rs, hf', hty, hn, -⟩ := hz
  obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans hf)
  obtain ⟨ps', rs', he', hpl, -⟩ := expand_of_funcType hty
  have hstep : HEvStep P (answerAt host m) (callAt z F')
      (some ⟨(m.1, z.2.2, z.2.1), (z.2.2, .trap)⟩) ⟨z.2.2, F', Result.trap.toAdmin⟩ := by
    rw [callAt_code hf]
    exact hEvStep_host_call hf he' (hn.trans (by rw [← hpl])) hcode
      (Or.inr ⟨rfl, hzs, hzu, by rw [hzs]⟩)
  obtain ⟨E, a', hd, hst, -, -⟩ := hV _ _ _ hstep
  refine ⟨V (callAt z F'), E, a', evRun_of_answerAt run hc, ?_, ?_⟩
  · rw [← hzu]; exact hd
  · exact hst.symm.trans hzs

end Silmaril.Proofs.Wasm.Abstract.HostClosingInf
