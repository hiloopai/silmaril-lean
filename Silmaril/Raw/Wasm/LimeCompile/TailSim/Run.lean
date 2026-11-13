module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.Basic
public import Silmaril.Wasm.Execution.Core.Sim.Context

/-!
# The two-way simulation of the tail-call rewrite: runs of the non-local shapes

At every profile and host:

* `fill_step`, `fill_steps`, `fill_trans`: steps lift through a nest of labels (`NCtx`);
* `step_mid`, `trans_mid`: steps lift through a value prefix and a suffix;
* `bubble`: a kernel that leaves a label with its values (`return`, `return_call_ref`) leaves a
  whole nest of labels;
* `TA.run`, `TT.run`: a trap-active (throw-active) sequence reduces to `trap` (the throw);
* `TA.fill`, `TT.fill`: activity is kept under a nest;
* `wrap_ret`: a wrapper frame whose innermost label holds `val^k RETURN` returns those values.

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim (Step.append_right Step.vals_left vals_nil' vals_cons')
open Silmaril.Wasm.LimeCompile.TailSim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- A step in a value prefix and a suffix. -/
theorem step_mid {s s' : Store H} {g g' : Frame} {Y Y' : List Admin}
    (h : Step P host ⟨s, g, Y⟩ ⟨s', g', Y'⟩) (pre : List Val) (rest : List Admin) :
    Step P host ⟨s, g, vals pre ++ Y ++ rest⟩ ⟨s', g', vals pre ++ Y' ++ rest⟩ :=
  Step.append_right (Step.vals_left h pre) rest

/-- A non-empty run in a value prefix and a suffix. -/
theorem trans_mid {s s' : Store H} {g g' : Frame} {Y Y' : List Admin}
    (h : Relation.TransGen (Step P host) ⟨s, g, Y⟩ ⟨s', g', Y'⟩) (pre : List Val)
    (rest : List Admin) :
    Relation.TransGen (Step P host) ⟨s, g, vals pre ++ Y ++ rest⟩ ⟨s', g', vals pre ++ Y' ++ rest⟩ :=
  Relation.TransGen.lift (p := Step P host) (fun c : Config H => (⟨c.store, c.frame, vals pre ++ c.code ++ rest⟩ : Config H))
    (fun a b hs => by
      rcases a with ⟨sa, fa, ia⟩; rcases b with ⟨sb, fb, ib⟩; exact step_mid hs pre rest) _ _ h

/-- A non-empty run inside a frame. -/
theorem trans_frame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {Y Y' : List Admin}
    (h : Relation.TransGen (Step P host) ⟨s, fi, Y⟩ ⟨s', fi', Y'⟩) :
    Relation.TransGen (Step P host) ⟨s, f, [.frame n fi Y]⟩ ⟨s', f, [.frame n fi' Y']⟩ :=
  Relation.TransGen.lift (p := Step P host) (fun c : Config H => (⟨c.store, f, [.frame n c.frame c.code]⟩ : Config H))
    (fun a b hs => by
      rcases a with ⟨sa, fa, ia⟩; rcases b with ⟨sb, fb, ib⟩; exact .ctxtFrame hs) _ _ h

/-- A non-empty run inside a label. -/
theorem trans_label {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr}
    {Y Y' : List Admin} (h : Relation.TransGen (Step P host) ⟨s, f, Y⟩ ⟨s', f', Y'⟩) :
    Relation.TransGen (Step P host) ⟨s, f, [.label n cont Y]⟩ ⟨s', f', [.label n cont Y']⟩ :=
  Relation.TransGen.lift (p := Step P host) (fun c : Config H => (⟨c.store, c.frame, [.label n cont c.code]⟩ : Config H))
    (fun a b hs => by
      rcases a with ⟨sa, fa, ia⟩; rcases b with ⟨sb, fb, ib⟩; exact .ctxtLabel hs) _ _ h

/-- A non-empty run inside a handler. -/
theorem trans_handler {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch}
    {Y Y' : List Admin} (h : Relation.TransGen (Step P host) ⟨s, f, Y⟩ ⟨s', f', Y'⟩) :
    Relation.TransGen (Step P host) ⟨s, f, [.handler n cs Y]⟩ ⟨s', f', [.handler n cs Y']⟩ :=
  Relation.TransGen.lift (p := Step P host) (fun c : Config H => (⟨c.store, c.frame, [.handler n cs c.code]⟩ : Config H))
    (fun a b hs => by
      rcases a with ⟨sa, fa, ia⟩; rcases b with ⟨sb, fb, ib⟩; exact .ctxtHandler hs) _ _ h

/-! ## Nests of labels -/

/-- **Steps lift through a nest of labels.** -/
theorem fill_step {s s' : Store H} {g g' : Frame} {X X' : List Admin}
    (h : Step P host ⟨s, g, X⟩ ⟨s', g', X'⟩) :
    ∀ N : NCtx, Step P host ⟨s, g, N.fill X⟩ ⟨s', g', N.fill X'⟩
  | .hole => h
  | .label V n cont N L => by
    have := step_mid (Step.ctxtLabel (n := n) (cont := cont) (fill_step h N)) V L
    simpa [NCtx.fill] using this

theorem fill_steps {s s' : Store H} {g g' : Frame} {X X' : List Admin}
    (h : Steps P host ⟨s, g, X⟩ ⟨s', g', X'⟩) (N : NCtx) :
    Steps P host ⟨s, g, N.fill X⟩ ⟨s', g', N.fill X'⟩ :=
  Relation.ReflTransGen.lift (fun c : Config H => (⟨c.store, c.frame, N.fill c.code⟩ : Config H))
    (fun a b hs => by
      rcases a with ⟨sa, fa, ia⟩; rcases b with ⟨sb, fb, ib⟩; exact fill_step hs N) _ _ h

theorem fill_trans {s s' : Store H} {g g' : Frame} {X X' : List Admin}
    (h : Relation.TransGen (Step P host) ⟨s, g, X⟩ ⟨s', g', X'⟩) (N : NCtx) :
    Relation.TransGen (Step P host) ⟨s, g, N.fill X⟩ ⟨s', g', N.fill X'⟩ :=
  Relation.TransGen.lift (p := Step P host) (fun c : Config H => (⟨c.store, c.frame, N.fill c.code⟩ : Config H))
    (fun a b hs => by
      rcases a with ⟨sa, fa, ia⟩; rcases b with ⟨sb, fb, ib⟩; exact fill_step hs N) _ _ h

/-- **Bubbling a kernel out of a nest of labels.** A kernel `κ` that leaves a label keeping the
values before it leaves every nest; the values of the nest accumulate in front of it. -/
theorem bubble {κ : Admin}
    (hlab : ∀ (s : Store H) (g : Frame) (n : Nat) (cont : List Instr) (vs : List Val)
      (rest : List Admin),
      Step P host ⟨s, g, [.label n cont (vals vs ++ [κ] ++ rest)]⟩ ⟨s, g, vals vs ++ [κ]⟩)
    (s : Store H) (g : Frame) :
    ∀ (N : NCtx) (W : List Val) (Y : List Admin),
      ∃ (W₀ : List Val) (Y' : List Admin),
        Steps P host ⟨s, g, N.fill (vals W ++ κ :: Y)⟩ ⟨s, g, vals (W₀ ++ W) ++ κ :: Y'⟩
  | .hole, W, Y => ⟨[], Y, by simpa [NCtx.fill] using (Relation.ReflTransGen.refl :
      Steps P host ⟨s, g, vals W ++ κ :: Y⟩ _)⟩
  | .label V n cont N L, W, Y => by
    obtain ⟨W₀, Y', h⟩ := bubble hlab s g N W Y
    have hin : Steps P host ⟨s, g, (NCtx.label V n cont N L).fill (vals W ++ κ :: Y)⟩
        ⟨s, g, vals V ++ [.label n cont (vals (W₀ ++ W) ++ [κ] ++ Y')] ++ L⟩ := by
      have h' := Steps.ctxtInstrs (vs := V) (rest := L) (Steps.label (n := n) (cont := cont) h)
      simpa [NCtx.fill] using h'
    have hout := step_mid (hlab s g n cont (W₀ ++ W) Y') V L
    refine ⟨V ++ W₀, L, ?_⟩
    have e : vals V ++ (vals (W₀ ++ W) ++ [κ]) ++ L = vals (V ++ W₀ ++ W) ++ κ :: L := by simp
    rw [e] at hout
    exact hin.tail hout

/-- `RETURN` leaves a label with its values. -/
theorem return_label (s : Store H) (g : Frame) (n : Nat) (cont : List Instr) (vs : List Val)
    (rest : List Admin) :
    Step P host ⟨s, g, [.label n cont (vals vs ++ [.plain .return_] ++ rest)]⟩
      ⟨s, g, vals vs ++ [.plain .return_]⟩ := .returnLabel

/-- **A wrapper returns its callee's values**: a frame of arity `k` whose innermost label holds
`val^k RETURN` reduces to those values. -/
theorem wrap_ret {s : Store H} {f fi : Frame} {k : Nat} (N : NCtx) (pre ws : List Val)
    (Y : List Admin) (hk : ws.length = k) :
    Relation.TransGen (Step P host)
      ⟨s, f, [.frame k fi (N.fill (vals pre ++ vals ws ++ .plain .return_ :: Y))]⟩
      ⟨s, f, vals ws⟩ := by
  obtain ⟨W₀, Y', h⟩ := bubble (P := P) (host := host) return_label s fi N (pre ++ ws) Y
  have h₁ : Steps P host ⟨s, f, [.frame k fi (N.fill (vals pre ++ vals ws ++ .plain .return_ :: Y))]⟩
      ⟨s, f, [.frame k fi (vals (W₀ ++ pre) ++ vals ws ++ [.plain .return_] ++ Y')]⟩ := by
    have h' := Steps.frame (f := f) (n := k) h
    simpa using h'
  exact Relation.TransGen.tail' h₁ (Step.returnFrame hk)

/-! ## Trap- and throw-active code -/

/-- Discarding around a trap. -/
theorem disc_trap (s : Store H) (g : Frame) (W : List Val) (Y : List Admin) :
    Steps P host ⟨s, g, vals W ++ .trap :: Y⟩ ⟨s, g, [.trap]⟩ := by
  by_cases hne : W ≠ [] ∨ Y ≠ []
  · have := Step.trapInstrs (P := P) (host := host) (s := s) (f := g) (vs := W) (rest := Y) hne
    simpa using Relation.ReflTransGen.single this
  · have hW : W = [] := by simpa using (not_or.mp hne).1
    have hY : Y = [] := by simpa using (not_or.mp hne).2
    subst hW hY
    exact .refl

/-- Discarding around a thrown exception. -/
theorem disc_throw (a : Nat) (s : Store H) (g : Frame) (W : List Val) (Y : List Admin) :
    Steps P host ⟨s, g, vals W ++ throwing a ++ Y⟩ ⟨s, g, throwing a⟩ := by
  by_cases hne : W ≠ [] ∨ Y ≠ []
  · exact .single (.throwRefInstrs hne)
  · have hW : W = [] := by simpa using (not_or.mp hne).1
    have hY : Y = [] := by simpa using (not_or.mp hne).2
    subst hW hY
    simpa [Sim.vals_nil'] using (Relation.ReflTransGen.refl : Steps P host ⟨s, g, throwing a⟩ _)

/-- **A trap-active sequence reduces to `trap`.** -/
theorem TA.run {s : Store H} {g : Frame} : ∀ {y : List Admin}, TA y →
    Steps P host ⟨s, g, y⟩ ⟨s, g, [.trap]⟩
  | _, .base ws y => disc_trap s g ws y
  | _, .label ws n cont y hb => by
    have h₁ := Steps.ctxtInstrs (vs := ws) (rest := y) (Steps.label (n := n) (cont := cont)
      (TA.run (s := s) (g := g) hb))
    have h₂ := step_mid (Step.trapLabel (P := P) (host := host) (s := s) (f := g) (n := n)
      (cont := cont)) ws y
    have h₃ : Steps P host ⟨s, g, vals ws ++ [.trap] ++ y⟩ ⟨s, g, [.trap]⟩ := by
      simpa using disc_trap (P := P) (host := host) s g ws y
    simpa using (h₁.tail h₂).trans h₃
  | _, .frame ws n fi y hb => by
    have h₁ := Steps.ctxtInstrs (vs := ws) (rest := y) (Steps.frame (f := g) (n := n)
      (TA.run (s := s) (g := fi) hb))
    have h₂ := step_mid (Step.trapFrame (P := P) (host := host) (s := s) (f := g) (fi := fi)
      (n := n)) ws y
    have h₃ : Steps P host ⟨s, g, vals ws ++ [.trap] ++ y⟩ ⟨s, g, [.trap]⟩ := by
      simpa using disc_trap (P := P) (host := host) s g ws y
    simpa using (h₁.tail h₂).trans h₃

/-- **A throw-active sequence reduces to the throw.** -/
theorem TT.run {s : Store H} {g : Frame} {a : Nat} : ∀ {y : List Admin}, TT a y →
    Steps P host ⟨s, g, y⟩ ⟨s, g, throwing a⟩
  | _, .base ws y => disc_throw a s g ws y
  | _, .label ws n cont y hb => by
    have h₁ := Steps.ctxtInstrs (vs := ws) (rest := y) (Steps.label (n := n) (cont := cont)
      (TT.run (s := s) (g := g) hb))
    have h₂ := step_mid (Step.throwRefLabel (P := P) (host := host) (s := s) (f := g) (n := n)
      (cont := cont) (a := a)) ws y
    have h₃ : Steps P host ⟨s, g, vals ws ++ throwing a ++ y⟩ ⟨s, g, throwing a⟩ :=
      disc_throw (P := P) (host := host) a s g ws y
    simpa [throwing] using (h₁.tail h₂).trans h₃
  | _, .frame ws n fi y hb => by
    have h₁ := Steps.ctxtInstrs (vs := ws) (rest := y) (Steps.frame (f := g) (n := n)
      (TT.run (s := s) (g := fi) hb))
    have h₂ := step_mid (Step.throwRefFrame (P := P) (host := host) (s := s) (f := g) (fi := fi)
      (n := n) (a := a)) ws y
    have h₃ : Steps P host ⟨s, g, vals ws ++ throwing a ++ y⟩ ⟨s, g, throwing a⟩ :=
      disc_throw (P := P) (host := host) a s g ws y
    simpa [throwing] using (h₁.tail h₂).trans h₃

theorem TA.fill {X : List Admin} (h : TA X) : ∀ N : NCtx, TA (N.fill X)
  | .hole => h
  | .label V n cont N L => TA.label V n cont L (TA.fill h N)

theorem TT.fill {a : Nat} {X : List Admin} (h : TT a X) : ∀ N : NCtx, TT a (N.fill X)
  | .hole => h
  | .label V n cont N L => TT.label V n cont L (TT.fill h N)

/-- A wrapper frame around a trap-active body is trap-active. -/
theorem TA.wrap {k : Nat} {fi : Frame} {b : List Admin} (h : TA b) : TA [.frame k fi b] := by
  simpa [Sim.vals_nil'] using TA.frame [] k fi [] h

theorem TT.wrap {a k : Nat} {fi : Frame} {b : List Admin} (h : TT a b) : TT a [.frame k fi b] := by
  simpa [Sim.vals_nil'] using TT.frame [] k fi [] h

end Silmaril.Raw.Wasm.LimeCompile.TailSim
