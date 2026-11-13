module

public import Silmaril.Wasm.JcoTool.KCoreRun.Defs
public import Silmaril.Wasm.Execution.Core.Properties

/-!
# `HSteps`: lifting through evaluation contexts, and single instructions

`hsteps_ctx`, `hsteps_label`, `hsteps_frame`: a run of `HStep` lifts under values and code
after it, into a label and into a frame. `hstep_core`: an `HStep` is a Core `Step` against
the stateless host `hostAt` of its host-state transition (a host-free step against every host,
`Step.of_noHost`). Then one lemma per instruction of the fragment on the operand stack
`stackA ops` in an arbitrary frame: constants, `local.get/set`, `global.get/set`, the numeric
operators.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCoreRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Wasm.JcoTool.KCore (BI)
open Silmaril.Wasm.FX.Asyncify.Tool (W stackA)

variable {H : Type} {Pf : Profile} {hb : BI → H} {ma : Nat}

/-- No host. -/
abbrev noHost : HostSemantics H := fun _ _ _ _ => False

/-! ## Contexts -/

theorem hstep_ctx {q q' : HQ} {s s' : Store H} {f f' : Frame} {X Y : List Admin} (vs : List Val)
    (rest : List Admin) (h : HStep Pf hb ma (q, ⟨s, f, X⟩) (q', ⟨s', f', Y⟩)) :
    HStep Pf hb ma (q, ⟨s, f, vals vs ++ X ++ rest⟩) (q', ⟨s', f', vals vs ++ Y ++ rest⟩) := by
  by_cases hv : vs = [] ∧ rest = []
  · obtain ⟨rfl, rfl⟩ := hv
    simpa only [vals, List.map_nil, List.nil_append, List.append_nil] using h
  · have hne : vs ≠ [] ∨ rest ≠ [] := by
      by_cases h1 : vs = []
      · exact .inr fun h2 => hv ⟨h1, h2⟩
      · exact .inl h1
    exact .instrs h hne

/-- The map of a context under values `vs` and code `rest`. -/
def inCtx (vs : List Val) (rest : List Admin) (x : HQ × Config H) : HQ × Config H :=
  (x.1, ⟨x.2.store, x.2.frame, vals vs ++ x.2.code ++ rest⟩)

theorem hsteps_ctx {q q' : HQ} {s s' : Store H} {f f' : Frame} {X Y : List Admin}
    (vs : List Val) (rest : List Admin)
    (h : HSteps Pf hb ma (q, ⟨s, f, X⟩) (q', ⟨s', f', Y⟩)) :
    HSteps Pf hb ma (q, ⟨s, f, vals vs ++ X ++ rest⟩) (q', ⟨s', f', vals vs ++ Y ++ rest⟩) := by
  refine Relation.ReflTransGen.lift (inCtx vs rest) (fun a b hab => ?_) _ _ h
  rcases a with ⟨qa, sa, fa, ia⟩
  rcases b with ⟨qb, sb, fb, ib⟩
  exact hstep_ctx vs rest hab

/-- `hsteps_ctx` with no values below. -/
theorem hsteps_app {q q' : HQ} {s s' : Store H} {f f' : Frame} {X Y : List Admin}
    (rest : List Admin) (h : HSteps Pf hb ma (q, ⟨s, f, X⟩) (q', ⟨s', f', Y⟩)) :
    HSteps Pf hb ma (q, ⟨s, f, X ++ rest⟩) (q', ⟨s', f', Y ++ rest⟩) := by
  simpa [vals] using hsteps_ctx (vs := []) rest h

/-- The map into a label. -/
def inLabel (n : Nat) (cont : List Instr) (x : HQ × Config H) : HQ × Config H :=
  (x.1, ⟨x.2.store, x.2.frame, [.label n cont x.2.code]⟩)

theorem hsteps_label {q q' : HQ} {s s' : Store H} {f f' : Frame} {X Y : List Admin} (n : Nat)
    (cont : List Instr) (h : HSteps Pf hb ma (q, ⟨s, f, X⟩) (q', ⟨s', f', Y⟩)) :
    HSteps Pf hb ma (q, ⟨s, f, [.label n cont X]⟩) (q', ⟨s', f', [.label n cont Y]⟩) := by
  refine Relation.ReflTransGen.lift (inLabel n cont) (fun a b hab => ?_) _ _ h
  rcases a with ⟨qa, sa, fa, ia⟩
  rcases b with ⟨qb, sb, fb, ib⟩
  exact .label hab

/-- The map into a frame. -/
def inFrame (f : Frame) (n : Nat) (x : HQ × Config H) : HQ × Config H :=
  (x.1, ⟨x.2.store, f, [.frame n x.2.frame x.2.code]⟩)

theorem hsteps_frame {q q' : HQ} {s s' : Store H} {fi fi' : Frame} {X Y : List Admin} (f : Frame)
    (n : Nat) (h : HSteps Pf hb ma (q, ⟨s, fi, X⟩) (q', ⟨s', fi', Y⟩)) :
    HSteps Pf hb ma (q, ⟨s, f, [.frame n fi X]⟩) (q', ⟨s', f, [.frame n fi' Y]⟩) := by
  refine Relation.ReflTransGen.lift (inFrame f n) (fun a b hab => ?_) _ _ h
  rcases a with ⟨qa, sa, fa, ia⟩
  rcases b with ⟨qb, sb, fb, ib⟩
  exact .frame hab

/-- One host-free Core step. -/
theorem hcore {q : HQ} {C C' : Config H} (h : Step Pf noHost C C') :
    HSteps Pf hb ma (q, C) (q, C') :=
  .single (.core h)

/-! ## `HStep` is Core's `Step` -/

/-- **An `HStep` is a Core 3.0 `Step`** against the stateless host of its host-state
transition. -/
theorem hstep_core {x y : HQ × Config H} (h : HStep Pf hb ma x y) :
    Step Pf (hostAt hb ma x.1 y.1) x.2 y.2 := by
  induction h with
  | core h => exact Step.of_noHost _ h
  | @host q q' s s' f c args res a fi ps rs b hc hf he hn hcode hans =>
    have hn' : (args.map Val.i32).length = ps.length := by rw [List.length_map]; exact hn
    have hh : hostAt hb ma q q' (hb b) s (args.map Val.i32) (.returned s' (.values (res.map Val.i32))) :=
      ⟨b, args, s', res, rfl, rfl, hans, rfl⟩
    exact .callRefHost (r := .values (res.map Val.i32)) hc hf he hn' hcode hh
  | instrs _ hne ih => exact .ctxtInstrs ih hne
  | label _ ih => exact .ctxtLabel ih
  | frame _ ih => exact .ctxtFrame ih

/-! ## The operand stack -/

theorem stackA_cons (v : W) (ops : List W) :
    stackA (v :: ops) = stackA ops ++ [(Val.i32 v).toAdmin] := by
  simp [stackA, vals]

theorem i32_toAdmin (v : W) : (Val.i32 v).toAdmin = .plain (.intConst .i32 v) := rfl

/-- A step on the top of the stack, under the stack and the code after it. -/
theorem top {q : HQ} {s s' : Store H} {f f' : Frame} {X Y : List Admin} (ops : List W)
    (rest : List Admin) (h : Step Pf noHost ⟨s, f, X⟩ ⟨s', f', Y⟩) :
    HSteps Pf hb ma (q, ⟨s, f, stackA ops ++ X ++ rest⟩) (q, ⟨s', f', stackA ops ++ Y ++ rest⟩) :=
  hsteps_ctx _ rest (hcore h)

/-- A constant is a value. -/
theorem const_val (b : W) (ops : List W) (rest : List Admin) :
    stackA ops ++ Admin.plain (.intConst .i32 b) :: rest = stackA (b :: ops) ++ rest := by
  rw [stackA_cons, List.append_assoc]
  rfl

theorem r_unop {q : HQ} {s : Store H} {f : Frame} {i : Instr} {x r : W} (ops : List W)
    (rest : List Admin) (h : NumericStep Pf [(Val.i32 x).toAdmin, .plain i] [(Val.i32 r).toAdmin]) :
    HSteps Pf hb ma (q, ⟨s, f, stackA (x :: ops) ++ .plain i :: rest⟩)
      (q, ⟨s, f, stackA (r :: ops) ++ rest⟩) := by
  have e₁ : stackA (x :: ops) ++ .plain i :: rest =
      stackA ops ++ [(Val.i32 x).toAdmin, .plain i] ++ rest := by
    rw [stackA_cons]; simp
  have e₂ : stackA (r :: ops) ++ rest = stackA ops ++ [(Val.i32 r).toAdmin] ++ rest := by
    rw [stackA_cons]
  rw [e₁, e₂]
  exact top ops rest (.numeric h)

theorem r_binop {q : HQ} {s : Store H} {f : Frame} {i : Instr} {x y r : W} (ops : List W)
    (rest : List Admin)
    (h : NumericStep Pf [(Val.i32 x).toAdmin, (Val.i32 y).toAdmin, .plain i] [(Val.i32 r).toAdmin]) :
    HSteps Pf hb ma (q, ⟨s, f, stackA (y :: x :: ops) ++ .plain i :: rest⟩)
      (q, ⟨s, f, stackA (r :: ops) ++ rest⟩) := by
  have e₁ : stackA (y :: x :: ops) ++ .plain i :: rest =
      stackA ops ++ [(Val.i32 x).toAdmin, (Val.i32 y).toAdmin, .plain i] ++ rest := by
    rw [stackA_cons, stackA_cons]; simp
  have e₂ : stackA (r :: ops) ++ rest = stackA ops ++ [(Val.i32 r).toAdmin] ++ rest := by
    rw [stackA_cons]
  rw [e₁, e₂]
  exact top ops rest (.numeric h)

theorem r_lget {q : HQ} {s : Store H} {f : Frame} {x : LocalIdx} {v : W}
    (hx : f.local? x = some (some (Val.i32 v))) (ops : List W) (rest : List Admin) :
    HSteps Pf hb ma (q, ⟨s, f, stackA ops ++ .plain (.localGet x) :: rest⟩)
      (q, ⟨s, f, stackA (v :: ops) ++ rest⟩) := by
  have e₂ : stackA (v :: ops) ++ rest = stackA ops ++ [(Val.i32 v).toAdmin] ++ rest := by
    rw [stackA_cons]
  rw [e₂, ← List.singleton_append, ← List.append_assoc]
  exact top ops rest (.variable (.localGet hx))

theorem r_gget {q : HQ} {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    {v : W} (hx : s.global? f x = some (a, g)) (hv : g.value = Val.i32 v) (ops : List W)
    (rest : List Admin) :
    HSteps Pf hb ma (q, ⟨s, f, stackA ops ++ .plain (.globalGet x) :: rest⟩)
      (q, ⟨s, f, stackA (v :: ops) ++ rest⟩) := by
  have e₂ : stackA (v :: ops) ++ rest = stackA ops ++ [g.value.toAdmin] ++ rest := by
    rw [stackA_cons, hv]
  rw [e₂, ← List.singleton_append, ← List.append_assoc]
  exact top ops rest (.variable (.globalGet hx))

theorem r_lset {q : HQ} {s : Store H} {f : Frame} {x : LocalIdx} {v : W}
    (hx : x.toNat < f.locals.length) (ops : List W) (rest : List Admin) :
    HSteps Pf hb ma (q, ⟨s, f, stackA (v :: ops) ++ .plain (.localSet x) :: rest⟩)
      (q, ⟨s, f.setLocal x (Val.i32 v), stackA ops ++ rest⟩) := by
  have e₁ : stackA (v :: ops) ++ .plain (.localSet x) :: rest =
      stackA ops ++ [(Val.i32 v).toAdmin, .plain (.localSet x)] ++ rest := by
    rw [stackA_cons]; simp
  rw [e₁]
  simpa using top (q := q) (hb := hb) (ma := ma) ops rest (.variable (.localSet (s := s) (v := Val.i32 v) hx))

theorem r_gset {q : HQ} {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    {v : W} (hx : s.global? f x = some (a, g)) (ops : List W) (rest : List Admin) :
    HSteps Pf hb ma (q, ⟨s, f, stackA (v :: ops) ++ .plain (.globalSet x) :: rest⟩)
      (q, ⟨s.setGlobal a (Val.i32 v), f, stackA ops ++ rest⟩) := by
  have e₁ : stackA (v :: ops) ++ .plain (.globalSet x) :: rest =
      stackA ops ++ [(Val.i32 v).toAdmin, .plain (.globalSet x)] ++ rest := by
    rw [stackA_cons]; simp
  rw [e₁]
  simpa using top (q := q) (hb := hb) (ma := ma) ops rest
    (.variable (.globalSet (f := f) (v := Val.i32 v) hx))

end Silmaril.Proofs.Wasm.JcoTool.KCoreRun
