module

public import Silmaril.Proofs.Wasm.Models.FXLower.Lower
public import Silmaril.Proofs.Wasm.Models.FXLower.HandlerEq
public import Silmaril.Proofs.Wasm.Models.FXLower.Complete
public import Silmaril.Proofs.Wasm.Models.FXLower.ContStuck

/-!
# Lowering WasmFX to Wasm: resuming a fresh continuation of a Core function is a call

The header of the first WasmFX → Wasm compilation (`Defs`).

* `behaviours_handler_sub`: a handler frame around Core code adds no restriction: every Core
  behaviour of `c` (with host `blockFX host fx`) is a CoreFX behaviour of `c` under a handler
  frame, with any continuation store;
* `src_steps`: `vs; ref.func a; cont.new; resume` runs in two steps to `vs; ref.func a; call_ref`
  under the resume's handler frame;
* **`lower_sound`**: every Core behaviour of the target is a CoreFX behaviour of the source.
  This is the soundness direction of compiler correctness (the compiled code only does what the
  source may do). No hypothesis on the host or the FX function table is needed.
* `stepFX_conservativeK`: track H's one-step conservativity, with any continuation store;
* **`behaviours_onHandler`** (no host calls, no FX functions): a handler frame around Core code
  is transparent, its CoreFX behaviours are exactly the Core behaviours, with any continuation
  store. The proof inverts the FX steps of `[handler hs (cs.map core)]`; a `br` or `return` that
  escapes the frame leaves stuck code on both sides;
* **`lower_after_admin`**: so after its two administrative steps the source has exactly the
  target's behaviours;
* **`behaviours_underHW`** (no host calls, no FX functions): values in front of a handler frame
  around Core code commute into it: the CoreFX behaviours of `W; handler hs (cs)` are Core
  behaviours of `W; cs`;
* **`lower_complete`** (no host calls, no FX functions): the converse of `lower_sound`. The
  untyped `resume` may split the operand stack `vs = W₁ ++ W₂` anywhere (no arity check), but
  every split runs to `W₁; handler (W₂; ref.func a; call_ref)`, which `behaviours_underHW` sends
  back to the target. The proof inverts the source's steps with a first-non-value
  decomposition for FX code (`fnvX`);
* **`lower_correct`**: hence the source and the target have equal behaviours;
* **`suspend_to_label`, `suspend_to_label_stuck`**: a defect of the FX model, found while
  preparing the next fragment (abortive handlers to `try_table`/`throw`). No `StepFX` rule moves
  a continuation reference (they move Core values `cvals` only), so the branch
  `vs; ref.cont k; br l` that `suspend` leaves for an `(on x l)` clause is stuck: the smallest
  abortive handler has no behaviours after it suspends.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXLower

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-- **A handler frame around Core code keeps every Core behaviour.** -/
theorem behaviours_handler_sub (K : List (Option ContFX)) (hs : List HClause) (s : Store H)
    (f : Frame) (cs : List Admin) :
    behavioursOf P (blockFX host fx) ⟨s, f, cs⟩ ⊆
      behavioursFX P host fx ⟨s, K, f, onHandler hs cs⟩ :=
  Silmaril.Proofs.Wasm.Models.FXLower.behaviours_handler_sub K hs ⟨s, f, cs⟩

/-- The source runs in two steps to the target under a handler frame. -/
theorem src_steps {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct : TypeIdx} {hs : List OnClause} {hs' : List HClause} {vs : List Val}
    (hf : s.funcs[a]? = some fi) (hr : hs.mapM (resolve s f) = some hs') :
    StepsFX P host fx ⟨s, K, f, srcResume a ct hs vs⟩
      ⟨s, Silmaril.Proofs.Wasm.Models.FXLower.kAfter K a fi.type, f,
        onHandler hs' (tgtCall a fi.type vs)⟩ :=
  Silmaril.Proofs.Wasm.Models.FXLower.src_steps hf hr

/-- **Soundness of the lowering** `resume (cont.new (ref.func a))` ↦ `call_ref`: every Core
behaviour of the target is a CoreFX behaviour of the source. -/
theorem lower_sound {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct : TypeIdx} {hs : List OnClause} {hs' : List HClause} {vs : List Val}
    (hf : s.funcs[a]? = some fi) (hr : hs.mapM (resolve s f) = some hs') :
    behavioursOf P (blockFX host fx) ⟨s, f, tgtCall a fi.type vs⟩ ⊆
      behavioursFX P host fx ⟨s, K, f, srcResume a ct hs vs⟩ :=
  Silmaril.Proofs.Wasm.Models.FXLower.lower_sound hf hr

/-- Without FX functions, the target's Core behaviours are taken with the host itself. -/
theorem lower_sound_noFX {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct : TypeIdx} {hs : List OnClause} {hs' : List HClause} {vs : List Val}
    (hf : s.funcs[a]? = some fi) (hr : hs.mapM (resolve s f) = some hs') :
    behavioursOf P host ⟨s, f, tgtCall a fi.type vs⟩ ⊆
      behavioursFX P host noFX ⟨s, K, f, srcResume a ct hs vs⟩ := by
  have h := lower_sound (P := P) (host := host) (fx := noFX) (K := K) (ct := ct) (vs := vs) hf hr
  rwa [blockFX_noFX] at h

/-- **Conservativity with live continuations**: on Core code whose store has no FX functions, the
CoreFX steps with any continuation store `K` are the Core steps, and keep `K`. -/
theorem stepFX_conservativeK {K : List (Option ContFX)} {c : Config H}
    (hno : NoFX fx c.store) {y : ConfigFX H} :
    StepFX P host fx (Silmaril.Proofs.Wasm.Models.FXLower.ofCoreK K c) y ↔
      ∃ c', Step P (blockFX host fx) c c' ∧ y = Silmaril.Proofs.Wasm.Models.FXLower.ofCoreK K c' :=
  ⟨fun h => Silmaril.Proofs.Wasm.Models.FXLower.step_ofCoreK h K c rfl hno,
    fun ⟨_, h, hy⟩ => hy ▸ Silmaril.Proofs.Wasm.Models.FXLower.ofCoreK_step h⟩

open Silmaril.Wasm.SingleThreaded.Det (noHost)

/-- **A handler frame around Core code is transparent** (no host calls, no FX functions). -/
theorem behaviours_onHandler (K : List (Option ContFX)) (hs : List HClause) (s : Store H)
    (f : Frame) (cs : List Admin) :
    behavioursFX P noHost noFX ⟨s, K, f, onHandler hs cs⟩ = behavioursOf P noHost ⟨s, f, cs⟩ :=
  Silmaril.Proofs.Wasm.Models.FXLower.behaviours_underH K hs ⟨s, f, cs⟩

/-- **After its two administrative steps, the source has exactly the target's behaviours** (no
host calls, no FX functions). -/
theorem lower_after_admin {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {hs' : List HClause} {vs : List Val} :
    behavioursFX P noHost noFX ⟨s, Silmaril.Proofs.Wasm.Models.FXLower.kAfter K a fi.type, f,
        onHandler hs' (tgtCall a fi.type vs)⟩ =
      behavioursOf P noHost ⟨s, f, tgtCall a fi.type vs⟩ :=
  behaviours_onHandler _ _ _ _ _

/-- **Values in front of a handler frame commute into it** (no host calls, no FX functions). -/
theorem behaviours_underHW (K : List (Option ContFX)) (hs : List HClause) (W : List Val)
    (s : Store H) (f : Frame) (cs : List Admin) :
    behavioursFX P noHost noFX ⟨s, K, f, cvals W ++ onHandler hs cs⟩ ⊆
      behavioursOf P noHost ⟨s, f, vals W ++ cs⟩ :=
  Silmaril.Proofs.Wasm.Models.FXLower.behaviours_underHW K hs W ⟨s, f, cs⟩

/-- **Completeness of the lowering** (no host calls, no FX functions): every CoreFX behaviour of
the source is a Core behaviour of the target. No arity check on `resume` is needed. -/
theorem lower_complete {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct : TypeIdx} {hs : List OnClause} {vs : List Val}
    (hf : s.funcs[a]? = some fi) :
    behavioursFX P noHost noFX ⟨s, K, f, srcResume a ct hs vs⟩ ⊆
      behavioursOf P noHost ⟨s, f, tgtCall a fi.type vs⟩ :=
  Silmaril.Proofs.Wasm.Models.FXLower.lower_complete hf

/-- **Correctness of the lowering** `resume (cont.new (ref.func a))` ↦ `call_ref` (no host
calls, no FX functions): equal behaviours. -/
theorem lower_correct {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct : TypeIdx} {hs : List OnClause} {hs' : List HClause} {vs : List Val}
    (hf : s.funcs[a]? = some fi) (hr : hs.mapM (resolve s f) = some hs') :
    behavioursFX P noHost noFX ⟨s, K, f, srcResume a ct hs vs⟩ =
      behavioursOf P noHost ⟨s, f, tgtCall a fi.type vs⟩ :=
  Silmaril.Proofs.Wasm.Models.FXLower.lower_correct hf hr

/-- **`suspend` to an `(on x l)` clause branches to the label with the continuation** -/
theorem suspend_to_label {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
    {k : List InstrFX} {hs : List HClause} {vs : List Val} {x : TagIdx} {ta : Nat}
    {ti : TagInst} {l : LabelIdx} (ht : s.tag? f x = some (ta, ti))
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) :
    StepFX P noHost fx ⟨s, K, f, Silmaril.Proofs.Wasm.Models.FXLower.abortSrc n k hs vs x⟩
      ⟨s, K ++ [some ⟨Ctx.hole.plug⟩], f,
        [.label n k (cvals vs ++ .contRef K.length :: [.core (.plain (.br l))])]⟩ :=
  Silmaril.Proofs.Wasm.Models.FXLower.suspend_to_label ht hc

/-- **… and that branch is stuck** (a defect of the FX model: `contRef` is not a value). -/
theorem suspend_to_label_stuck (s : Store H) (K : List (Option ContFX)) (f : Frame) (n : Nat)
    (k : List InstrFX) (vs : List Val) (j : Nat) (l : LabelIdx) :
    behavioursFX P noHost fx
      ⟨s, K, f, [.label n k (cvals vs ++ .contRef j :: [.core (.plain (.br l))])]⟩ = ∅ :=
  Silmaril.Proofs.Wasm.Models.FXLower.suspend_to_label_stuck s K f n k vs j l

/-- info: 'Silmaril.Wasm.Models.FXLower.lower_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lower_correct

/-- info: 'Silmaril.Wasm.Models.FXLower.lower_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lower_sound

/-- info: 'Silmaril.Wasm.Models.FXLower.behaviours_onHandler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms behaviours_onHandler

/-- info: 'Silmaril.Wasm.Models.FXLower.lower_after_admin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lower_after_admin

end Silmaril.Wasm.Models.FXLower
