module

public import Silmaril.Wasm.FX.Asyncify.Tool.CoreSim.Defs
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Core.Pure

/-!
# Core 3.0 runs inside the frames and levels of `CRel`

Runs lift through value contexts, labels and frames (`steps_instrs`, `steps_label`,
`steps_frame`), hence through the levels of a frame (`steps_wrap`) and the frames below
(`steps_stackC`, `steps_top`). A trap reaches the top (`trap_top`); `return` and the end of a
body leave a frame with its results (`ret_frameA`, `end_frameA`); an empty innermost arm is
closed (`pop_level`); a call of a defined function opens its frame (`call_frame`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.FX.Asyncify.Tool
open Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Core

variable {H : Type} {Pf : Profile} {host : HostSemantics H}

local notation "Steps" => Execution.Core.Steps Pf host

/-! ## Contexts -/

theorem lift_steps (φ : Config H → Config H)
    (hφ : ∀ c c', Step Pf host c c' → Step Pf host (φ c) (φ c')) {c c' : Config H}
    (h : Steps c c') : Steps (φ c) (φ c') := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (hφ _ _ hs)

theorem steps_instrs {s s' : Store H} {f f' : Silmaril.Wasm.Execution.Core.Frame}
    {X Y : List Admin} (vs : List Val) (rest : List Admin) (h : Steps ⟨s, f, X⟩ ⟨s', f', Y⟩) :
    Steps ⟨s, f, vals vs ++ X ++ rest⟩ ⟨s', f', vals vs ++ Y ++ rest⟩ :=
  lift_steps (fun c => ⟨c.store, c.frame, vals vs ++ c.code ++ rest⟩)
    (fun ⟨_, _, _⟩ ⟨_, _, _⟩ hs => step_ctx vs rest hs) h

theorem steps_label {s s' : Store H} {f f' : Silmaril.Wasm.Execution.Core.Frame}
    {X Y : List Admin} (n : Nat) (cont : List Instr) (h : Steps ⟨s, f, X⟩ ⟨s', f', Y⟩) :
    Steps ⟨s, f, [.label n cont X]⟩ ⟨s', f', [.label n cont Y]⟩ :=
  lift_steps (fun c => ⟨c.store, c.frame, [.label n cont c.code]⟩)
    (fun ⟨_, _, _⟩ ⟨_, _, _⟩ hs => .ctxtLabel hs) h

theorem steps_frame {s s' : Store H} {fi fi' : Silmaril.Wasm.Execution.Core.Frame}
    {X Y : List Admin} (f : Silmaril.Wasm.Execution.Core.Frame) (n : Nat)
    (h : Steps ⟨s, fi, X⟩ ⟨s', fi', Y⟩) :
    Steps ⟨s, f, [.frame n fi X]⟩ ⟨s', f, [.frame n fi' Y]⟩ :=
  lift_steps (fun c => ⟨c.store, f, [.frame n c.frame c.code]⟩)
    (fun ⟨_, _, _⟩ ⟨_, _, _⟩ hs => .ctxtFrame hs) h

theorem steps_wrap {s s' : Store H} {f f' : Silmaril.Wasm.Execution.Core.Frame} :
    ∀ (ls : List Lvl) {Z Z' : List Admin}, Steps ⟨s, f, Z⟩ ⟨s', f', Z'⟩ →
      Steps ⟨s, f, wrapL Z ls⟩ ⟨s', f', wrapL Z' ls⟩
  | [], _, _, h => h
  | l :: ls, _, _, h => steps_wrap ls (by
      simpa only [stackA, List.singleton_append, List.append_assoc] using
        steps_instrs (l.ops.reverse.map Val.i32) (expression l.code) (steps_label 0 [] h))

theorem steps_frameA {s s' : Store H} {mi : ModuleInst} {n : Nat} {l l' : List W}
    {Z Z' : List Admin} (h : Steps ⟨s, localsF ⟨[], mi⟩ l, Z⟩ ⟨s', localsF ⟨[], mi⟩ l', Z'⟩)
    (f : Silmaril.Wasm.Execution.Core.Frame) :
    Steps ⟨s, f, [frameA mi n l Z]⟩ ⟨s', f, [frameA mi n l' Z']⟩ :=
  steps_frame f n (steps_label n [] h)

/-- Runs of the callee's frame lift into the frames below. -/
theorem steps_stackC {s s' : Store H} {mi : ModuleInst} :
    ∀ (fss : List CFr) {X X' : List Admin},
      (∀ f, Steps ⟨s, f, X⟩ ⟨s', f, X'⟩) →
      ∀ f, Steps ⟨s, f, stackC mi fss X⟩ ⟨s', f, stackC mi fss X'⟩
  | [], _, _, h => h
  | fs :: rest, X, X', h => by
    have h1 : ∀ f, Steps ⟨s, f, [fs.admin mi X]⟩ ⟨s', f, [fs.admin mi X']⟩ := fun f => by
      have h2 : Steps ⟨s, localsF ⟨[], mi⟩ fs.locals, stackA fs.l0.ops ++ X ++ expression fs.l0.code⟩
          ⟨s', localsF ⟨[], mi⟩ fs.locals, stackA fs.l0.ops ++ X' ++ expression fs.l0.code⟩ :=
        steps_instrs _ _ (h _)
      exact steps_frameA (steps_wrap fs.ls h2) f
    exact steps_stackC rest h1

/-- A run inside the innermost level of the top frame lifts to the whole configuration. -/
theorem steps_top {s s' : Store H} {mi : ModuleInst} {n : Nat} {l l' : List W}
    {Z Z' : List Admin} (rest : List CFr) (ls : List Lvl)
    (h : Steps ⟨s, localsF ⟨[], mi⟩ l, Z⟩ ⟨s', localsF ⟨[], mi⟩ l', Z'⟩)
    (g : Silmaril.Wasm.Execution.Core.Frame) :
    Steps ⟨s, g, stackC mi rest [frameA mi n l (wrapL Z ls)]⟩
      ⟨s', g, stackC mi rest [frameA mi n l' (wrapL Z' ls)]⟩ :=
  steps_stackC rest (steps_frameA (steps_wrap ls h)) g

/-! ## Traps -/

theorem trap_vals {s : Store H} {f : Silmaril.Wasm.Execution.Core.Frame} (vs : List Val)
    (rest : List Admin) : Steps ⟨s, f, vals vs ++ [.trap] ++ rest⟩ ⟨s, f, [.trap]⟩ := by
  by_cases hv : vs = [] ∧ rest = []
  · obtain ⟨rfl, rfl⟩ := hv
    exact .refl
  · have hne : vs ≠ [] ∨ rest ≠ [] := by
      by_cases h1 : vs = []
      · exact .inr fun h2 => hv ⟨h1, h2⟩
      · exact .inl h1
    exact .single (.trapInstrs hne)

theorem trap_wrap {s : Store H} {f : Silmaril.Wasm.Execution.Core.Frame} :
    ∀ ls : List Lvl, Steps ⟨s, f, wrapL [.trap] ls⟩ ⟨s, f, [.trap]⟩
  | [] => .refl
  | l :: ls => by
    have h1 : Steps ⟨s, f, stackA l.ops ++ .label 0 [] [.trap] :: expression l.code⟩
        ⟨s, f, [.trap]⟩ := by
      have h := steps_instrs (s := s) (f := f) (Pf := Pf) (host := host)
        (l.ops.reverse.map Val.i32) (expression l.code) (.single (Step.trapLabel (n := 0) (cont := [])))
      have h' := h.trans (trap_vals _ _)
      simpa only [stackA, List.singleton_append, List.append_assoc] using h'
    exact (steps_wrap ls h1).trans (trap_wrap ls)

theorem trap_frameA {s : Store H} {f : Silmaril.Wasm.Execution.Core.Frame} (mi : ModuleInst)
    (n : Nat) (l : List W) : Steps ⟨s, f, [frameA mi n l [.trap]]⟩ ⟨s, f, [.trap]⟩ :=
  (steps_frame f n (steps_label n [] .refl |>.tail .trapLabel)).tail .trapFrame

theorem trap_stackC {s : Store H} {mi : ModuleInst} :
    ∀ (fss : List CFr) (f : Silmaril.Wasm.Execution.Core.Frame),
      Steps ⟨s, f, stackC mi fss [.trap]⟩ ⟨s, f, [.trap]⟩
  | [], _ => .refl
  | fs :: rest, f => by
    have h1 : ∀ g, Steps ⟨s, g, [fs.admin mi [.trap]]⟩ ⟨s, g, [.trap]⟩ := fun g =>
      (steps_frameA ((steps_wrap fs.ls (trap_vals _ _)).trans (trap_wrap fs.ls)) g).trans
        (trap_frameA mi _ _)
    exact (steps_stackC rest h1 f).trans (trap_stackC rest f)

/-- A trap in the innermost level of the top frame is a trap of the whole configuration. -/
theorem trap_top {s : Store H} {mi : ModuleInst} {n : Nat} {l : List W} (rest : List CFr)
    (ls : List Lvl) (vs : List Val) (R : List Admin) (g : Silmaril.Wasm.Execution.Core.Frame) :
    Steps ⟨s, g, stackC mi rest [frameA mi n l (wrapL (vals vs ++ [.trap] ++ R) ls)]⟩
      ⟨s, g, [.trap]⟩ := by
  have h1 : ∀ f, Steps ⟨s, f, [frameA mi n l (wrapL (vals vs ++ [.trap] ++ R) ls)]⟩
      ⟨s, f, [.trap]⟩ := fun f =>
    (steps_frameA ((steps_wrap ls (trap_vals vs R)).trans (trap_wrap ls)) f).trans
      (trap_frameA mi n l)
  exact (steps_stackC rest h1 g).trans (trap_stackC rest g)

/-! ## Leaving a frame -/

theorem ret_wrap {s : Store H} {f : Silmaril.Wasm.Execution.Core.Frame} :
    ∀ (ls : List Lvl) (V : List Val) (R : List Admin), ∃ V' R',
      Steps ⟨s, f, wrapL (vals V ++ [.plain .return_] ++ R) ls⟩
        ⟨s, f, vals (V' ++ V) ++ [.plain .return_] ++ R'⟩
  | [], V, R => ⟨[], R, by simpa using .refl⟩
  | l :: ls, V, R => by
    have h1 : Steps ⟨s, f, stackA l.ops ++ .label 0 [] (vals V ++ [.plain .return_] ++ R) ::
        expression l.code⟩
        ⟨s, f, vals (l.ops.reverse.map Val.i32 ++ V) ++ [.plain .return_] ++ expression l.code⟩ := by
      simpa only [stackA, vals_append, List.singleton_append, List.append_assoc] using
        steps_instrs (s := s) (f := f) (Pf := Pf) (host := host) (l.ops.reverse.map Val.i32)
          (expression l.code) (.single .returnLabel)
    obtain ⟨V', R', h2⟩ := ret_wrap (s := s) (f := f) ls (l.ops.reverse.map Val.i32 ++ V)
      (expression l.code)
    exact ⟨V' ++ l.ops.reverse.map Val.i32, R', (steps_wrap ls h1).trans
      (by simpa only [List.append_assoc] using h2)⟩

/-- A `return` with the results `vs` on top leaves the frame. -/
theorem ret_frameA {s : Store H} (f : Silmaril.Wasm.Execution.Core.Frame) (mi : ModuleInst)
    {n : Nat} (l : List W) (ls : List Lvl) (V vs : List Val) (R : List Admin)
    (hn : vs.length = n) :
    Steps ⟨s, f, [frameA mi n l (wrapL (vals (V ++ vs) ++ [.plain .return_] ++ R) ls)]⟩
      ⟨s, f, vals vs⟩ := by
  obtain ⟨V', R', h1⟩ := ret_wrap (s := s) (f := localsF ⟨[], mi⟩ l) (Pf := Pf) (host := host)
    ls (V ++ vs) R
  have h2 : Steps ⟨s, localsF ⟨[], mi⟩ l, [.label n [] (vals (V' ++ (V ++ vs)) ++
      [.plain .return_] ++ R')]⟩
      ⟨s, localsF ⟨[], mi⟩ l, vals (V' ++ V) ++ vals vs ++ [.plain .return_] ++ []⟩ := by
    simpa only [vals_append, List.append_assoc, List.append_nil] using
      Relation.ReflTransGen.single (Step.returnLabel (P := Pf) (host := host) (s := s)
        (f := localsF ⟨[], mi⟩ l) (n := n) (cont := []) (vs := V' ++ (V ++ vs)) (rest := R'))
  exact (steps_frame f n ((steps_label n [] h1).trans h2)).tail (.returnFrame hn)

/-- The end of a body with exactly the results `vs` leaves the frame. -/
theorem end_frameA {s : Store H} (f : Silmaril.Wasm.Execution.Core.Frame) (mi : ModuleInst)
    {n : Nat} (l : List W) (vs : List Val) (hn : vs.length = n) :
    Steps ⟨s, f, [frameA mi n l (vals vs)]⟩ ⟨s, f, vals vs⟩ :=
  (steps_frame f n (.single .labelVals)).tail (.frameVals hn)

/-- An empty innermost arm is closed. -/
theorem pop_level {s : Store H} {f : Silmaril.Wasm.Execution.Core.Frame} (l : Lvl)
    (ls : List Lvl) :
    Steps ⟨s, f, wrapL [] (l :: ls)⟩ ⟨s, f, wrapL (stackA l.ops ++ expression l.code) ls⟩ := by
  have h : Steps ⟨s, f, stackA l.ops ++ .label 0 [] [] :: expression l.code⟩
      ⟨s, f, stackA l.ops ++ expression l.code⟩ := by
    simpa only [stackA, List.singleton_append, List.append_assoc, vals, List.map_nil,
      List.nil_append] using steps_instrs (s := s) (f := f) (Pf := Pf) (host := host)
        (l.ops.reverse.map Val.i32) (expression l.code)
        (.single (Step.labelVals (n := 0) (cont := []) (vs := [])))
  exact steps_wrap ls h

/-! ## Calls -/

theorem forCall_eq (mi : ModuleInst) (args : List W) (n : Nat) :
    Frame.forCall mi (args.map Val.i32) (List.replicate n .i32) =
      localsF ⟨[], mi⟩ (args ++ List.replicate n 0) := by
  simp only [Frame.forCall, localsF, List.map_append, List.map_map, List.map_replicate]
  rfl

/-- A call of a defined function opens its frame. -/
theorem call_frame {s : Store H} {f : Silmaril.Wasm.Execution.Core.Frame} {mi : ModuleInst}
    {E : Env} (hH : HoldsProg s mi E) (hf : f.module = mi) {j : Nat} {fd : FnDef}
    (hj : E.fns[j]? = some fd) {x : FuncIdx} (hx : x.toNat = E.imps.length + j) {args : List W}
    (ha : args.length = fd.nparams) :
    Steps ⟨s, f, vals (args.map Val.i32) ++ [.plain (.call x)]⟩
      ⟨s, f, [frameA mi fd.nres (args ++ List.replicate fd.nlocals 0) (expression fd.body)]⟩ := by
  obtain ⟨a, fi, ty, ps, rs, hfa, hfi, hmod, hcode, hexp, hps, hrs⟩ := hH j fd hj
  have h1 : Step Pf host ⟨s, f, [.plain (.call x)]⟩
      ⟨s, f, [.ref (.func a), .callRefType fi.type]⟩ :=
    .call (by rw [hf, hx]; exact hfa) hfi
  have h2 := Step.callRefFunc (P := Pf) (host := host) (s := s) (f := f)
    (c := .callRefType fi.type) (vs := args.map Val.i32) trivial hfi hexp
    (by rw [List.length_map, ha, hps]) hcode
  have h3 : Steps ⟨s, f, vals (args.map Val.i32) ++ [.plain (.call x)]⟩
      ⟨s, f, vals (args.map Val.i32) ++ [.ref (.func a), .callRefType fi.type]⟩ := by
    simpa only [List.append_nil] using
      steps_instrs (args.map Val.i32) [] (.single h1)
  refine h3.tail ?_
  rw [hmod, forCall_eq, hrs] at h2
  exact h2

end Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim
