module

public import Silmaril.Semantics.TraceModels.Defs
public import Silmaril.Proofs.Semantics.TraceModels.OrderedLog
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Traces
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Iteration
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Algebra
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Codiagonal
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Naturality
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Uniformity
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Laws
import all Silmaril.Proofs.Semantics.TraceModels.OrderedLog
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Traces
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Iteration
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Algebra
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Codiagonal
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Naturality
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Uniformity
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Laws
import Batteries.Tactic.Alias

/-!
# Infinite output streams: proofs

Proofs for `Silmaril.Semantics.TraceModels.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.PartialWriter

open ContinuousLog

variable {W : Type} [Monoid W]

private theorem Prefix.stream_product (ws : ℕ → W) {a z : ℕ} {w : W}
    (hp : Prefix (stream ws) a w z) : prefixProd ws a * w = prefixProd ws z := by
  induction hp with
  | start a => simp
  | @step a a' z w hs _ ih =>
      have heq : a' = a + 1 := Sum.inr.inj (_root_.Part.mem_some_iff.mp hs)
      subst a'
      simpa only [stream, done, ← mul_assoc, ← prefixProd_succ] using ih
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.Prefix.stream_product := Silmaril.Elgot.PartialWriter.Prefix.stream_product

private theorem stream_prefix (ws : ℕ → W) (n : ℕ) :
    Prefix (stream ws) 0 (prefixProd ws n) n := by
  induction n with
  | zero => exact .start 0
  | succ n ih =>
      exact ih.snoc (_root_.Part.mem_some (Sum.inr (n + 1) : PUnit ⊕ ℕ))
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.stream_prefix := Silmaril.Elgot.PartialWriter.stream_prefix

private theorem stream_no_run (ws : ℕ → W) {a : ℕ} {w : W} {b : PUnit}
    (hr : Runs (stream ws) a w b) : False := by
  induction hr with
  | done hs => cases _root_.Part.mem_some_iff.mp hs
  | step _ _ ih => exact ih
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.stream_no_run := Silmaril.Elgot.PartialWriter.stream_no_run

variable [CompleteLattice W] [ContinuousLog W]

private theorem iterOutput_stream (ws : ℕ → W) :
    iterOutput (stream ws) 0 = omegaProduct ws := by
  apply le_antisymm
  · apply iterOutput_le
    intro w z hp
    have hw : w = prefixProd ws z := by simpa using hp.stream_product ws
    rw [hw]
    exact prefixProd_le_omegaProduct ws (z + 1)
  · apply iSup_le
    intro n
    cases n with
    | zero => exact ContinuousLog.one_le _
    | succ n => exact le_iterOutput (stream_prefix ws n)
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.iterOutput_stream := Silmaril.Elgot.PartialWriter.iterOutput_stream

private theorem iter_stream (ws : ℕ → W) :
    iter (stream ws) 0 = diverge (omegaProduct ws) := by
  apply ext
  · apply _root_.Part.eq_none_iff.mpr
    intro b hb
    rcases (mem_value_iter_iff (stream ws) 0 b).mp hb with ⟨w, hr⟩
    exact stream_no_run ws hr
  · exact iterOutput_stream ws
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.iter_stream := Silmaril.Elgot.PartialWriter.iter_stream

private theorem iter_emit_forever (w : W) (a : PUnit) :
    iter (fun a : PUnit => done (Sum.inr a : PUnit ⊕ PUnit) w) a =
      diverge (omegaProduct (fun _ => w)) := by
  have h := congrFun (uniformity (stream (fun _ => w))
    (fun a : PUnit => done (Sum.inr a : PUnit ⊕ PUnit) w) (fun _ => a) (by
      funext n
      simp [Bind.kleisliRight, liftPure, stream, bind, done])) 0
  simpa only [Bind.kleisliRight, liftPure, Function.comp_def, LawfulMonad.pure_bind, iter_stream] using h.symm
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.iter_emit_forever := Silmaril.Elgot.PartialWriter.iter_emit_forever

end Silmaril.Elgot.PartialWriter
