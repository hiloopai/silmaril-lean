module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.FwdInf

/-!
# The converse bridge: productive native runs are productive Core runs (proofs)

* `descends_fwd`, `descPath_fwd`: a descent (path) of `wasmHOpen` from a typed call is a Core
  run with exactly its import calls, from the call into the reached call, inside the callee
  frames and labels entered on the way; the reached call is typed;
* `infLw_fwd`: a resolved productive run of a Wasm body is a productive Core run of its call;
* `infChain_fwd`: an infinite chain of descents is a chain of Core runs nested ever deeper
  (`coreInf_of_segments`);
* `wasmEvInfN_coreInf` (**the converse bridge**, every profile, the native host slice, checked
  stores, typed invocations): every productive run of `wasmEvInfN` whose answers the host
  allows is a productive Core run of the invocation with exactly those events.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInf

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Interp
open Shape (streamAppend StreamConcat SubstInf Res1 SubstPre)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- **A descent of the module is a Core run with its import calls**, from the caller's call
into the reached call, inside the callee's frame and label. -/
theorem descends_fwd (hH : Interp.NativeHostSlice host) {x y : (wasmHShape H).self.Op}
    {q : List (Call (wasmHostSig H))}
    (h : Shape.Descends wasmHOpen (Shape.close wasmHOpen) x q y) (hc : Cons host q)
    (hx : InvC x) :
    InvC y ∧ ∀ g : Frame, ∃ (F' : Frame) (V : Config H → Config H), Lifts P host V ∧
      EvRun P host (callAt x g) q (V (callAt y F')) := by
  obtain ⟨fi, fn, ps, rs, l, hf, hcode, hty, hr, hq⟩ := descends_unwrap h
  obtain ⟨fi', ps', rs', hf', hty', hn, hS⟩ := hx
  obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans hf)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty.symm.trans hty'))
  obtain ⟨ob, hbc⟩ := body_chk hS hf hcode hty hn
  obtain ⟨hy, W, F', hW, run⟩ := reachL_fwd (P := P) hH hr q hq hc hS hbc
  refine ⟨hy, fun g => ⟨F', _, lifts_comp (lifts_frame rs.length g)
    (lifts_comp (lifts_label rs.length []) hW), ?_⟩⟩
  exact evRun_trans (evRun_of_free (enter_body (P := P) hf hcode hty hn g))
    (evRun_wrap _ (lifts_frame (P := P) (host := host) rs.length g)
      (evRun_wrap _ (lifts_label (P := P) (host := host) rs.length []) run))

/-- **A descent path is a Core run with its import calls.** -/
theorem descPath_fwd (hH : Interp.NativeHostSlice host) {x z : (wasmHShape H).self.Op}
    {qs : List (Call (wasmHostSig H))}
    (h : Shape.DescPath wasmHOpen (Shape.close wasmHOpen) x qs z) :
    Cons host qs → InvC x →
      InvC z ∧ ∀ g : Frame, ∃ (F' : Frame) (V : Config H → Config H), Lifts P host V ∧
        EvRun P host (callAt x g) qs (V (callAt z F')) := by
  induction h with
  | refl x => exact fun _ hx => ⟨hx, fun g => ⟨g, fun c => c, lifts_id, .refl _⟩⟩
  | step hd _ ih =>
    intro hc hx
    rw [cons_append] at hc
    obtain ⟨hy, D⟩ := descends_fwd (P := P) hH hd hc.1 hx
    obtain ⟨hz, E⟩ := ih hc.2 hy
    refine ⟨hz, fun g => ?_⟩
    obtain ⟨F₁, V₁, hV₁, r₁⟩ := D g
    obtain ⟨F₂, V₂, hV₂, r₂⟩ := E F₁
    exact ⟨F₂, fun c => V₁ (V₂ c), lifts_comp hV₁ hV₂, evRun_trans r₁ (evRun_wrap V₁ hV₁ r₂)⟩

/-- **A resolved productive run of a Wasm body is a productive Core run of its call.** -/
theorem infLw_fwd (hH : Interp.NativeHostSlice host) {z : (wasmOShape H).self.Op}
    {ν : Nat → HCall H} {ω : Nat → Call (wasmHostSig H)} (hz : InvC z)
    (hν : ν ∈ InfLw z.1 z.2.2 z.2.1) (hs : SubstInf (Shape.close wasmHOpen) ν ω)
    (hc : ConsInf host ω) (g : Frame) : CoreInf P host (callAt z g) ω := by
  obtain ⟨fi, fn, ω₀, hf, hcode, hI, rfl⟩ := hν
  obtain ⟨fi', ps, rs, hf', hty, hn, hS⟩ := hz
  obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans hf)
  obtain ⟨ob, hbc⟩ := body_chk hS hf hcode hty hn
  have hinf := infL_fwd (P := P) hH hI ω hs hc hS hbc
  have := coreInf_prepend (evRun_of_free (enter_body (P := P) hf hcode hty hn g))
    (coreInf_frame (f := g) rs.length (coreInf_label rs.length [] hinf))
  simpa [Shape.streamAppend_nil] using this

/-- **An infinite chain of descents is a productive Core run**: the descents' Core runs, each
nested inside the callee frames entered so far. -/
theorem infChain_fwd (hH : Interp.NativeHostSlice host) {x : (wasmHShape H).self.Op}
    {ω : Nat → Call (wasmHostSig H)}
    (h : Shape.InfChain wasmHOpen (Shape.close wasmHOpen) x ω) (hc : ConsInf host ω)
    (hx : InvC x) (g₀ : Frame) : CoreInf P host (callAt x g₀) ω := by
  classical
  obtain ⟨gs, q, rfl, hd, hp, hu⟩ := h
  have hq : StreamConcat q ω := ⟨hp, hu⟩
  have hcq := cons_of_concat hq hc
  have inv : ∀ n, InvC (gs n) := by
    intro n
    induction n with
    | zero => exact hx
    | succ n ih => exact (descends_fwd (P := P) hH (hd n) (hcq n) ih).1
  have D := fun n => (descends_fwd (P := P) hH (hd n) (hcq n) (inv n)).2
  let F : Nat → Frame := fun n =>
    Nat.rec (motive := fun _ => Frame) g₀ (fun n Fn => Classical.choose (D n Fn)) n
  let V : Nat → Config H → Config H := fun n =>
    Classical.choose (Classical.choose_spec (D n (F n)))
  have hV : ∀ n, Lifts P host (V n) ∧
      EvRun P host (callAt (gs n) (F n)) (q n) (V n (callAt (gs (n + 1)) (F (n + 1)))) :=
    fun n => Classical.choose_spec (Classical.choose_spec (D n (F n)))
  let O : Nat → Config H → Config H := fun n =>
    Nat.rec (motive := fun _ => Config H → Config H) (fun c => c)
      (fun n On => fun c => On (V n c)) n
  have hO : ∀ n, Lifts P host (O n) := by
    intro n
    induction n with
    | zero => exact lifts_id
    | succ n ih => exact lifts_comp ih (hV n).1
  let K : Nat → Config H := fun n => O n (callAt (gs n) (F n))
  have seg : ∀ n, EvRun P host (K n) (q n) (K (n + 1)) :=
    fun n => evRun_wrap (O n) (hO n) (hV n).2
  exact coreInf_of_segments K q seg hq

/-- A typed invocation of a checked store is a typed call. -/
theorem invC_of_invokeOk {s : Store H} {a : Nat} {vs : List Val} (hS : StoreChk s.funcs)
    (hok : InvokeOk s a vs) : InvC (⟨a, (vs, s)⟩ : (wasmOShape H).self.Op) := by
  obtain ⟨fi, ps, rs, hfi, he, -⟩ := id hok
  have hty : Validation.DefType.funcType? fi.type = some (ps.toList, rs.toList) := by
    unfold Validation.DefType.funcType?; rw [Validation.Expand.iff.mp he]
  exact ⟨fi, _, _, hfi, hty, args_length hok hfi hty, hS⟩

/-- **The converse bridge** (every profile, the native host slice, checked stores, typed
invocations): every productive run of `wasmEvInfN` whose answers the host allows is a
productive Core run of the invocation with exactly those events. -/
theorem wasmEvInfN_coreInf (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat}
    {vs : List Val} (hS : StoreChk s.funcs) (hok : InvokeOk s a vs)
    {ω : Nat → Call (wasmHostSig H)} (h : ω ∈ wasmEvInfN s (a, vs)) (hc : ConsInf host ω) :
    CoreInf P host (invoke s a vs) ω := by
  have hx := invC_of_invokeOk hS hok
  change CoreInf P host (callAt ⟨a, (vs, s)⟩ {}) ω
  rcases h with hch | ⟨z, qs, ν, ω', hp, hν, hsi, rfl⟩
  · exact infChain_fwd hH hch hc hx {}
  · obtain ⟨hcq, hc'⟩ := consInf_split hc
    obtain ⟨hz, D⟩ := descPath_fwd (P := P) hH hp hcq hx
    obtain ⟨F', V, hV, run⟩ := D {}
    exact coreInf_prepend run (coreInf_wrap V hV (infLw_fwd hH hz hν hsi hc' F'))

end Silmaril.Proofs.Wasm.Abstract.HostClosingInf
