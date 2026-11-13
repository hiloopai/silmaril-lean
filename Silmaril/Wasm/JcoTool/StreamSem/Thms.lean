module

public import Silmaril.Wasm.JcoTool.StreamSem.Defs
public import Silmaril.Wasm.JcoTool.Tool.Thms
public import Silmaril.Wasm.Component.Streams.Proc.Thms

/-!
# Implementations of `Proc` transformers are correct, and what a stream output means

* `reachM_sim`: every system reachable through an implementation `I` of `tStep T N` is
  related, by `I.R`, to a system of `Proc` reachable with the same store, producer and
  consumer (the simulation is lifted to the interleavings of the three components).
* **`impl_correct`**, **`impl_safe`**: so `Proc.pipeline_correct` and `Proc.pipeline_safe`
  hold for every implementation: when everything has finished the consumer holds exactly
  `T.run cs.flatten`, and at every point a prefix of it, for every interleaving, chunking
  and read size.
* **`newWith_stream_semantics`**, at the entry point of `wasm-jco new`: for an output whose
  export `name` passes the shape check, the bytes are read back with their built-ins by
  `xparse`, the export is a `Proc`-shaped stream transformer (async lift, the read, write,
  new, drop and waitable-set built-ins at their canonical types, by `New.plan_ok`), and for
  every transformer `T` and every implementation of the export simulating `tStep T N`, the
  pipeline computes `T.run` of its input. That the module's export is such an implementation
  is the hypothesis, not proved (see the module docs of `StreamSem.Defs`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.StreamSem

open Silmaril.Wasm.Wit.Binary (World)
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Proc

variable {σ : Type} {T : Tr σ Val Val} {N : Nat}

/-- The `Proc` system of a machine system and a transformer counter. -/
def SysM.toSys {M : Type} (s : SysM M) (t : TPc σ) : Sys σ := ⟨s.st, s.p, t, s.c⟩

/-- One step of the machine pipeline is a step of the `Proc` pipeline, or a stutter. -/
theorem stepM_sim (I : Impl σ T N) {s s' : SysM I.M} {t : TPc σ} (hR : I.R s.m t)
    (h : StepM I s s') :
    ∃ t', I.R s'.m t' ∧ (Step T N (s.toSys t) (s'.toSys t') ∨ s.toSys t = s'.toSys t') := by
  cases h with
  | prod hp => exact ⟨t, hR, .inl (Step.prod hp)⟩
  | cons n hn hc => exact ⟨t, hR, .inl (Step.cons n hn hc)⟩
  | impl hm =>
    rcases I.step_R hR hm with ⟨t', ht, hR'⟩ | ⟨hst, hR'⟩
    · exact ⟨t', hR', .inl (Step.trans ht)⟩
    · refine ⟨t, hR', .inr ?_⟩
      show SysM.toSys s t = SysM.toSys { s with st := _, m := _ } t
      simp only [SysM.toSys, hst]

/-- **The simulation, lifted to reachability.** -/
theorem reachM_sim (I : Impl σ T N) {cs : List (List Val)} {s : SysM I.M} (h : ReachM I cs s) :
    ∃ t, I.R s.m t ∧ Reach T N cs (s.toSys t) := by
  obtain ⟨st₀, hst, hs⟩ := h
  induction hs with
  | refl => exact ⟨.rd T.init, I.init_R, st₀, hst, Steps.refl _⟩
  | tail _ hstep ih =>
    obtain ⟨t, hR, st₁, hst₁, hS⟩ := ih
    obtain ⟨t', hR', hor⟩ := stepM_sim I hR hstep
    refine ⟨t', hR', st₁, hst₁, ?_⟩
    rcases hor with hst' | e
    · exact Steps.tail hS hst'
    · exact e ▸ hS

/-- **Correctness of every implementation**: when the producer, the implementation and the
consumer have finished, the consumer holds exactly `T.run` of the concatenated input. -/
theorem impl_correct (I : Impl σ T N) (cs : List (List Val)) (s : SysM I.M) (h : ReachM I cs s)
    (hp : s.p = .fin) (hm : I.done s.m = true) (acc : List Val) (hc : s.c = .fin acc) :
    acc = T.run cs.flatten := by
  obtain ⟨t, hR, hr⟩ := reachM_sim I h
  have ht : t = .fin := I.done_R hR hm
  exact pipeline_correct T N cs (s.toSys t) hr hp ht acc hc

/-- **Safety of every implementation**: the consumer's items are always a prefix of `T.run`
of the concatenated input. -/
theorem impl_safe (I : Impl σ T N) (cs : List (List Val)) (s : SysM I.M) (h : ReachM I cs s)
    (acc : List Val)
    (hc : s.c = .recv acc ∨ s.c = .wait acc ∨ s.c = .close acc ∨ s.c = .fin acc) :
    acc <+: T.run cs.flatten := by
  obtain ⟨t, _, hr⟩ := reachM_sim I h
  exact pipeline_safe T N cs (s.toSys t) hr acc hc

/-- **The meaning of a stream output of `wasm-jco new`.** -/
theorem newWith_stream_semantics {core : ByteArray} {w : World} {o : Tool.Out}
    (h : Tool.newWith core w = .ok o) (name : String)
    (hs : ∀ p, New.plan core w = .ok p → xfShape p name = true) :
    (∃ p c, New.plan core w = .ok p ∧ New.emit p = .ok c ∧ xparse o.bytes = .ok c.norm ∧
      xfShape p name = true ∧
      List.Forall₂ (New.ReqOk p.imports p.exports) (p.mod.importNames.zip p.mod.imports) p.reqs ∧
      List.Forall₂ (New.LiftOk p.mod) p.exports p.lifts) ∧
    ∀ (σ : Type) (T : Tr σ Val Val) (N : Nat) (I : Impl σ T N) (cs : List (List Val))
      (s : SysM I.M), ReachM I cs s → s.p = .fin → I.done s.m = true →
      ∀ acc, s.c = .fin acc → acc = T.run cs.flatten := by
  obtain ⟨p, c, hp, hc, hx⟩ := Tool.newWith_xparse h
  have hok := New.plan_ok hp
  exact ⟨⟨p, c, hp, hc, hx, hs p hp, hok.2.2.2, hok.2.2.1⟩,
    fun _ T N I cs s hr hpf hm acc hacc => impl_correct I cs s hr hpf hm acc hacc⟩

/-- The model's own transformer is an implementation: the hypothesis is satisfiable. -/
theorem self_correct (T : Tr σ Val Val) (N : Nat) (cs : List (List Val)) (s : SysM (Impl.self T N).M)
    (h : ReachM (Impl.self T N) cs s) (hp : s.p = .fin) (hm : (Impl.self T N).done s.m = true)
    (acc : List Val) (hc : s.c = .fin acc) : acc = T.run cs.flatten :=
  impl_correct _ cs s h hp hm acc hc

end Silmaril.Wasm.JcoTool.StreamSem
