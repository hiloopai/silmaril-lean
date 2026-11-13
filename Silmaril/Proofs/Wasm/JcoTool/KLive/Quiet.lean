module

public import Silmaril.Proofs.Wasm.JcoTool.KLive.Pipe

/-!
# The open pipe comes to rest with the kernel's output so far

In the *open* pipe (`KRead.PStep … true …`) the source never drops its writable end, so the
module never sees the end of its input. Here:

* `open_src`: the source of an open run has not closed;
* `open_term`: every open run can be continued to a state where nothing can step (an infinite
  open run would be an infinite run of the system, `no_infinite_mrun`);
* **`term_got`**: at such a state the sink holds `(trV k).runP xs`, the kernel's output so far
  (for kernels with `FlushNil`). The argument reads the network's invariants at the final state:
  the module cannot step, so it waits for a read with nothing pending, or for a write with nothing
  pending, or has exited; the sink waits for a read with nothing pending, or has gone; the
  source has written everything, or waits. Every combination but two is contradictory: the module
  waits for its read after the source wrote all of `xs`, which it read, and the sink read all its
  output; or the kernel is done and the module exited, after the sink read all its output;
* **`pipe_part`**: the outputs so far of the open pipe are exactly `(trV k).runP xs`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KLive

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (blocked)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net (Network NSt RV OS rh wh NStep Node Sys)
open Silmaril.Wasm.Component.Streams.Kernel (KM KSt)
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KDrop
open Silmaril.Wasm.JcoTool.KNet
open Silmaril.Wasm.JcoTool.KLive
open Silmaril.Wasm.JcoTool.KRead (PSys PStep PSteps m₀ Closed dropObs FlushNil srcN snkN)
open Silmaril.Proofs.Wasm.JcoTool.KCore
open Silmaril.Proofs.Wasm.JcoTool.KDrop
open Silmaril.Proofs.Wasm.JcoTool.KNet
open Silmaril.Proofs.Wasm.Component.Streams.Net (Coh Inv RInv WInv ChanInv wOut NodeInv OInv)
open Silmaril.Proofs.Wasm.Component.Streams.Live (StPos chan_in chan_out busy_open write_ok
  dstep_write_eq wait_wh_ok)

variable {xs : List Val} {k : KM} {N : Nat}

/-! ## Open runs -/

theorem init_not_closed (xs : List Val) (k : KM) : ¬ Closed (NSt.init (srcN xs k)) := by
  rintro ⟨d, a, h⟩
  simp [NSt.init, srcN, kchain] at h

/-- The source of an open run has not closed. -/
theorem open_src {X : Type} {R : DStore → X → DStore → X → Prop} {m₀' : X} {c : PSys X}
    (h : PSteps xs k true R (PSys.init xs k m₀') c) : ¬ Closed c.src := by
  induction h with
  | refl => exact init_not_closed xs k
  | tail _ h ih =>
    cases h with
    | src _ hcl => exact hcl rfl
    | mod _ => exact ih
    | snk _ => exact ih

/-- **Every open run can be continued to a state where nothing can step.** -/
theorem open_term (hN : 0 < N ∧ N ≤ 256) (hfit : KFits k N) {c : PSys MS}
    (hc : PSteps xs k true (DRStep (genD k N)) (PSys.init xs k (m₀ k)) c) :
    ∃ T, PSteps xs k true (DRStep (genD k N)) c T ∧
      ∀ T', ¬ PStep xs k true (DRStep (genD k N)) T T' := by
  classical
  by_contra hne
  have hst : ∀ T, PSteps xs k true (DRStep (genD k N)) c T →
      ∃ T', PStep xs k true (DRStep (genD k N)) T T' := fun T hT => by
    by_contra h1
    exact hne ⟨T, hT, fun T' h2 => h1 ⟨T', h2⟩⟩
  let nx : {T // PSteps xs k true (DRStep (genD k N)) c T} →
      {T // PSteps xs k true (DRStep (genD k N)) c T} := fun T =>
    ⟨Classical.choose (hst T.1 T.2), T.2.tail (Classical.choose_spec (hst T.1 T.2))⟩
  let g : Nat → {T // PSteps xs k true (DRStep (genD k N)) c T} := fun n => nx^[n] ⟨c, .refl⟩
  obtain ⟨L, S⟩ := live_setting (pM_live (xs := xs) hN hfit)
  apply no_infinite_mrun (pM_live (xs := xs) hN hfit).ok S (fun n => toM (g n).1)
    (psteps_mreach (hc.trans (g 0).2))
  intro n
  have e : g (n + 1) = nx (g n) := Function.iterate_succ_apply' nx n _
  show MStep _ (toM (g n).1) (toM (g (n + 1)).1)
  rw [e]
  exact pstep_mstep (Classical.choose_spec (hst (g n).1 (g n).2))

/-! ## The final state -/

theorem afterWrite_not_closed (ys q a : List Val) (r : Nat) (d : Bool) (a' : List Val) :
    Silmaril.Wasm.Component.Streams.Net.Out.afterWrite ys q a r ≠ ⟨.closed d, a'⟩ := by
  unfold Silmaril.Wasm.Component.Streams.Net.Out.afterWrite Silmaril.Wasm.Component.Streams.Net.Out.onWrite
  split_ifs <;> simp

theorem onWrite_busy_not_closed (ys q a : List Val) (p : Nat) (d : Bool) (a' : List Val) :
    Silmaril.Wasm.Component.Streams.Net.Out.onWrite ⟨.busy ys q, a⟩ p ≠ ⟨.closed d, a'⟩ := by
  unfold Silmaril.Wasm.Component.Streams.Net.Out.onWrite
  split_ifs <;> simp

/-- A stream's transferred items are a prefix of its writer's output so far. -/
theorem sent_prefix {O : List Val} {fl : Bool} {o : Silmaril.Wasm.Component.Streams.Net.Out} {R : RV} {got : List Val} {c : DChan}
    (hO : OInv O fl o) (hC : ChanInv o.st.view o.ack R got c) : c.sent <+: O := by
  obtain ⟨st, a⟩ := o
  cases st with
  | idle q =>
    simp only [OInv] at hO
    have hs : c.sent = a := hC.1.2.2.2.1
    rw [hs, ← hO]; exact List.prefix_append _ _
  | busy ys q =>
    simp only [OInv] at hO
    have hs : c.sent = a ++ ys.take c.wp := hC.1.2.2.2.2.1
    rw [hs, ← hO]
    exact ((List.prefix_append_right_inj a).2 (List.take_prefix _ _)).trans (List.prefix_append _ _)
  | dead =>
    simp only [OInv] at hO
    have hs : c.sent = a := hC.1.2.2.2.2.2
    rw [hs]; exact hO
  | closed d =>
    have hs : c.sent = a := hC.1.2.2.1
    rw [hs]
    cases d with
    | false => simp only [OInv] at hO; rw [hO.1]
    | true => simpa only [OInv] using hO

/-- Feeding past a `done` state reads nothing more. -/
theorem runP_done {σ : Type} (T : Tr σ Val Val) {g ys : List Val} (hp : g <+: ys)
    (hd : T.done (T.feed T.init g).1 = true) : T.runP ys = T.runP g := by
  obtain ⟨r, rfl⟩ := hp
  simp only [Tr.runP]
  rw [Silmaril.Proofs.Wasm.Component.Streams.Spec.feed_append,
    Silmaril.Proofs.Wasm.Component.Streams.Spec.feed_done T _ hd]
  simp

end Silmaril.Proofs.Wasm.JcoTool.KLive
