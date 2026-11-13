module

public import Silmaril.Proofs.Wasm.Component.Streams.Net.Main
public import Silmaril.Wasm.Component.Streams.Spec.Thms

/-!
# From the invariant to the specification

`SpecOK s i L`: node `i` has read a prefix of `L`, and all of `L` if it saw the end of its input.
A source satisfies it with `L = []` (`src_spec`); if the writer of a node's input stream satisfies
it with `L`, the node satisfies it with the writer's `T.run L` (`node_spec`): what a node reads is
a prefix of what its writer has acknowledged, which is a prefix of the writer's output so far,
which is a prefix of `T.run L`, and all of it once the stream has ended (the writer then closed
normally, after its flush, and its flush is `T.run L`'s, since it dropped its input at the end or
when `T` was done).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Net

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Proofs.Wasm.Component.Streams.Spec

variable {net : Network} {σ : Type} {s : Sys net}

/-- Node `i` has read a prefix of `L`, and all of it if its input ended. -/
def SpecOK (s : Sys net) (i : Fin net.k) (L : List Val) : Prop :=
  (s.ns i).got <+: L ∧ ((s.ns i).rd = .gone true → (s.ns i).got = L)

/-- A flushed node's output so far is `T.run L`. -/
theorem out_flushed (N : Node) (x : NSt N.σ) (hN : NodeInv N x) (L : List Val)
    (hp : x.got <+: L) (he : x.rd = .gone true → x.got = L) (hf : x.flushedP N.T = true) :
    x.outSoFar N.T = N.T.run L := by
  have h1 : x.outSoFar N.T = N.T.run x.got := by
    simp only [NSt.outSoFar, hf, ↓reduceIte, Tr.run, hN.hs]
  rw [h1]
  unfold NSt.flushedP at hf
  split at hf
  · rename_i b hb
    cases b
    · have hd : N.T.done (N.T.feed N.T.init x.got).1 = true := by
        simpa [← hN.hs] using hf
      exact run_prefix_done N.T _ _ hd hp
    · rw [he hb]
  · cases hf

/-- A node's output so far is a prefix of `T.run L`, and all of it once flushed. -/
theorem out_spec (N : Node) (x : NSt N.σ) (hN : NodeInv N x) (L : List Val)
    (hp : x.got <+: L) (he : x.rd = .gone true → x.got = L) :
    x.outSoFar N.T <+: N.T.run L ∧ (x.flushedP N.T = true → x.outSoFar N.T = N.T.run L) := by
  refine ⟨?_, out_flushed N x hN L hp he⟩
  by_cases hf : x.flushedP N.T = true
  · exact out_flushed N x hN L hp he hf ▸ List.prefix_refl _
  · have hf' : x.flushedP N.T = false := by simpa using hf
    simp only [NSt.outSoFar, hf', Bool.false_eq_true, ↓reduceIte, List.append_nil]
    obtain ⟨X, rfl⟩ := hp
    exact (Tr.runP_mono N.T x.got X).trans (Tr.runP_le_run N.T _)

/-- What a reader has read is a prefix of the stream's transferred items. -/
theorem got_le_sent {R : RV} {got : List Val} {c : DChan} (hR : RInv R got c) :
    got <+: c.sent := by
  cases R with
  | idle => exact hR.1 ▸ List.prefix_refl _
  | busy => exact hR.1 ▸ List.prefix_append _ _
  | ended => exact hR.1 ▸ List.prefix_refl _
  | gone e => exact hR.1 ▸ List.prefix_refl _

/-- The transferred items are a prefix of the writer's output so far. -/
theorem sent_le_out {O : List Val} {fl : Bool} {o : Out} {c : DChan} (hO : OInv O fl o)
    (hW : WInv o.st.view o.ack c) : c.sent <+: O := by
  obtain ⟨st, a⟩ := o
  cases st with
  | idle q =>
    have hO' : a ++ q = O := hO
    rw [hW.2.2.2.1, ← hO']
    exact List.prefix_append _ _
  | busy xs q =>
    have hO' : a ++ xs ++ q = O := hO
    rw [hW.2.2.2.2.1, ← hO', List.append_assoc]
    exact (List.prefix_append_right_inj a).2 ((List.take_prefix _ _).trans (List.prefix_append _ _))
  | dead => exact hW.2.2.2.2.2 ▸ hO
  | closed d =>
    rw [hW.2.2.1]
    cases d
    · exact hO.1 ▸ List.prefix_refl _
    · exact hO

/-- What the reader of a stream has read is a prefix of what its writer acknowledged, which is a
prefix of the writer's output so far. -/
theorem got_le_out (hI : Inv net s) {c : Nat} (hc : c < net.m) :
    (s.ns (net.rd c)).got <+: (s.ns (net.wr c).1).outSoFar (net.node (net.wr c).1).T := by
  obtain ⟨o, ho, hW, hR, -, -⟩ := hI.chan c hc
  have hO := (hI.node (net.wr c).1).outs o (List.mem_of_getElem? ho)
  exact (got_le_sent hR).trans (sent_le_out hO hW)

/-- A writer that closed normally, after its flush, was flushed for its `T`'s output: it dropped
its input at the end or when `T` was done, not because every output was dead. -/
theorem flushed_of_closed {N : Node} {x : NSt N.σ} (hN : NodeInv N x) {j : Nat} {a : List Val}
    (ho : x.outs[j]? = some ⟨.closed false, a⟩) (hfl : x.rd.flushed = true) :
    x.flushedP N.T = true := by
  unfold RV.flushed at hfl
  unfold NSt.flushedP
  split at hfl
  · rename_i b hb
    cases b
    · rcases hN.stop hb with hT | ⟨-, hall⟩
      · simp [hT]
      · rcases hall _ (List.mem_of_getElem? ho) with h | h <;> cases h
    · rfl
  · cases hfl

/-- A reader that saw the end of its stream has read all of its writer's output, and the writer
has flushed. -/
theorem got_eof (hI : Inv net s) {c : Nat} (hc : c < net.m) (he : (s.ns (net.rd c)).rd = .gone true) :
    (s.ns (net.rd c)).got = (s.ns (net.wr c).1).outSoFar (net.node (net.wr c).1).T ∧
      (s.ns (net.wr c).1).flushedP (net.node (net.wr c).1).T = true := by
  obtain ⟨o, ho, hW, hR, -, hRL⟩ := hI.chan c hc
  rw [he] at hR hRL
  have hcl : o.st.view = .closed false := hRL (Or.inr rfl)
  have hN := hI.node (net.wr c).1
  have hO := hN.outs o (List.mem_of_getElem? ho)
  obtain ⟨st, a⟩ := o
  obtain rfl : st = .closed false := by
    cases st <;> simp only [OS.view, reduceCtorEq, WV.closed.injEq] at hcl
    rw [hcl]
  have hO' : a = _ ∧ _ := hO
  exact ⟨by rw [← hR.1, hW.2.2.1, hO'.1], flushed_of_closed hN ho hO'.2⟩

/-- A source has read nothing and seen the end. -/
theorem src_spec (hI : Inv net s) (i : Fin net.k) (h : (net.node i).inp = none) : SpecOK s i [] := by
  obtain ⟨h1, h2⟩ := (hI.node i).src h
  exact ⟨h2 ▸ List.prefix_refl _, fun _ => h2⟩

/-- **The specification propagates along a stream.** -/
theorem node_spec (hwf : net.WF) (hI : Inv net s) (i : Fin net.k) {c : Nat}
    (hinp : (net.node i).inp = some c) (L : List Val) (hU : SpecOK s (net.wr c).1 L) :
    SpecOK s i ((net.node (net.wr c).1).T.run L) := by
  obtain ⟨hm, hrd⟩ := hwf.inp_rd i c hinp
  have hO := out_spec _ _ (hI.node (net.wr c).1) L hU.1 hU.2
  have h1 := got_le_out hI hm
  rw [hrd] at h1
  refine ⟨h1.trans hO.1, fun he => ?_⟩
  have h2 := got_eof hI hm (by rw [hrd]; exact he)
  rw [hrd] at h2
  rw [h2.1, hO.2 h2.2]

/-- A node without outputs that is never done drops its input only at the end. -/
theorem sink_eof (hI : Inv net s) (i : Fin net.k) (hout : (net.node i).outs = [])
    (hnd : ∀ q, (net.node i).T.done q = false) {b : Bool} (h : (s.ns i).rd = .gone b) :
    b = true := by
  cases b
  · rcases (hI.node i).stop h with hT | ⟨hne, -⟩
    · rw [hnd] at hT
      cases hT
    · have := (hI.node i).len
      rw [hout] at this
      exact absurd (List.length_eq_zero_iff.1 this) hne
  · rfl

end Silmaril.Proofs.Wasm.Component.Streams.Net
