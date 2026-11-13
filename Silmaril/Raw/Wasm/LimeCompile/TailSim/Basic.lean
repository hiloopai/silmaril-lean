module

public import Silmaril.Wasm.LimeCompile.TailSim.Defs
public import Silmaril.Wasm.LimeCompile.Tail.Thms
public import Silmaril.Wasm.Execution.Core.Properties

/-!
# The two-way simulation of the tail-call rewrite: basic facts about the code relation

* `R.refl`: identical code is related (at both directions and both levels);
* `R.expr_tailL`: an instruction sequence is related to its tail rewrite;
* `R.append`, `R.vals`: the relation is closed under concatenation and value prefixes;
* `NCtx` facts (`fill_append`, `fill_step`, `fill_steps`), and appends for `PW`, `PT`, `TA`,
  `TT`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim (Step.append_right Step.vals_left vals_nil' vals_cons')
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)
open Silmaril.Wasm.LimeCompile.TailSim
open Silmaril.Proofs.Wasm.LimeCompile.Tail (tailL_nil tailL_cons tailL_append)

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-! ## Basic shapes -/

theorem Val.toAdmin_not_ctx (v : Val) : ¬ v.toAdmin.IsCtx := by
  rcases v with ⟨⟨_ | _, _⟩⟩ | _ | _ <;> simp [Val.toAdmin, Admin.IsCtx]

theorem plain_not_ctx (i : Instr) : ¬ (Admin.plain i).IsCtx := by simp [Admin.IsCtx]

theorem expression_cons (i : Instr) (is : List Instr) :
    expression (i :: is) = .plain i :: expression is := rfl

theorem expression_append (a b : List Instr) :
    expression (a ++ b) = expression a ++ expression b := List.map_append

/-! ## Reflexivity and the rewrite -/

/-- **Identical code is related.** -/
theorem R.refl (fw : Bool) : ∀ (tl : Bool) (x : List Admin), R fw tl x x
  | _, [] => .nil
  | tl, .label n cont b :: x => .label (Or.inl rfl) (R.refl fw tl b) (R.refl fw tl x)
  | tl, .handler n cs b :: x => .handler (R.refl fw false b) (R.refl fw tl x)
  | tl, .frame n fi b :: x =>
    .callee (xs := [.frame n fi b]) (ys := [.frame n fi b]) (.frame (R.refl fw true b))
      (R.refl fw tl x)
  | tl, .plain i :: x => .same (by simp [Admin.IsCtx]) (R.refl fw tl x)
  | tl, .ref r :: x => .same (by simp [Admin.IsCtx]) (R.refl fw tl x)
  | tl, .callRefType d :: x => .same (by simp [Admin.IsCtx]) (R.refl fw tl x)
  | tl, .returnCallRefType d :: x => .same (by simp [Admin.IsCtx]) (R.refl fw tl x)
  | tl, .trap :: x => .same (by simp [Admin.IsCtx]) (R.refl fw tl x)
termination_by _ x => sizeOf x

/-- **A sequence is related to its tail rewrite** (at tail-position level). -/
theorem R.expr_tailL (fw : Bool) : ∀ is : List Instr,
    R fw true (expression is) (expression (tailL is))
  | [] => by rw [tailL_nil]; exact .nil
  | i :: is => by
    rw [tailL_cons, expression_cons, expression_append]
    exact .instr (R.expr_tailL fw is)

/-- A label continuation and its related continuation, after values. -/
theorem R.cont {fw tl : Bool} {cont cont' : List Instr}
    (h : cont' = cont ∨ (tl = true ∧ cont' = tailL cont)) :
    R fw tl (expression cont) (expression cont') := by
  rcases h with rfl | ⟨rfl, rfl⟩
  · exact R.refl fw tl _
  · exact R.expr_tailL fw cont

/-! ## Nests of labels -/

theorem NCtx.fill_hole (X : List Admin) : NCtx.hole.fill X = X := rfl

theorem NCtx.fill_label (V : List Val) (n : Nat) (cont : List Instr) (N : NCtx) (L X : List Admin) :
    (NCtx.label V n cont N L).fill X = vals V ++ .label n cont (N.fill X) :: L := rfl

/-- Appending to a nest: either inside the hole (at the top level) or to the outer suffix. -/
def nApp : NCtx → List Admin → NCtx
  | .hole, _ => .hole
  | .label V n cont N L, y => .label V n cont N (L ++ y)

/-- The suffix that reaches the hole when appending to a nest. -/
def nInner : NCtx → List Admin → List Admin
  | .hole, y => y
  | .label _ _ _ _ _, _ => []

theorem NCtx.fill_append (N : NCtx) (X y : List Admin) :
    N.fill X ++ y = (nApp N y).fill (X ++ nInner N y) := by
  cases N with
  | hole => simp [NCtx.fill, nApp, nInner]
  | label V n cont N L => simp [NCtx.fill, nApp, nInner]

theorem PW.append {ys B : List Admin} (h : PW ys B) (y : List Admin) : PW ys (B ++ y) := by
  obtain ⟨N, pre, Y, rfl⟩ := h
  refine ⟨nApp N y, pre, Y ++ nInner N y, ?_⟩
  rw [NCtx.fill_append]
  simp

theorem PT.append {ws : List Val} {c : Admin} {B : List Admin} (h : PT ws c B) (y : List Admin) :
    PT ws c (B ++ y) := by
  obtain ⟨N, c', Y, hc, rfl⟩ := h
  refine ⟨nApp N y, c', Y ++ nInner N y, hc, ?_⟩
  rw [NCtx.fill_append]
  simp

theorem PTL.append {ws : List Val} {c : Admin} {B : List Admin} (h : PTL ws c B)
    (y : List Admin) : PTL ws c (B ++ y) := by
  obtain ⟨V, n, cont, N, L, c', Y, hc, rfl⟩ := h
  exact ⟨V, n, cont, N, L ++ y, c', Y, hc, by simp⟩

theorem PTL.prefix {ws : List Val} {c : Admin} {B : List Admin} (h : PTL ws c B)
    (W : List Val) : PTL ws c (vals W ++ B) := by
  obtain ⟨V, n, cont, N, L, c', Y, hc, rfl⟩ := h
  exact ⟨W ++ V, n, cont, N, L, c', Y, hc, by simp⟩

theorem PTL.toPT {ws : List Val} {c : Admin} {B : List Admin} (h : PTL ws c B) : PT ws c B := by
  obtain ⟨V, n, cont, N, L, c', Y, hc, rfl⟩ := h
  exact ⟨.label V n cont N L, c', Y, hc, rfl⟩

theorem TA.append {y : List Admin} (h : TA y) (z : List Admin) : TA (y ++ z) := by
  cases h with
  | base ws y => simpa using TA.base ws (y ++ z)
  | label ws n cont y hb => simpa using TA.label ws n cont (y ++ z) hb
  | frame ws n fi y hb => simpa using TA.frame ws n fi (y ++ z) hb

theorem TT.append {a : Nat} {y : List Admin} (h : TT a y) (z : List Admin) : TT a (y ++ z) := by
  cases h with
  | base ws y => simpa using TT.base (a := a) ws (y ++ z)
  | label ws n cont y hb => simpa using TT.label ws n cont (y ++ z) hb
  | frame ws n fi y hb => simpa using TT.frame ws n fi (y ++ z) hb

theorem TA.prefix {y : List Admin} (h : TA y) (V : List Val) : TA (vals V ++ y) := by
  cases h with
  | base ws y => simpa using TA.base (V ++ ws) y
  | label ws n cont y hb => simpa using TA.label (V ++ ws) n cont y hb
  | frame ws n fi y hb => simpa using TA.frame (V ++ ws) n fi y hb

theorem TT.prefix {a : Nat} {y : List Admin} (h : TT a y) (V : List Val) : TT a (vals V ++ y) := by
  cases h with
  | base ws y => simpa using TT.base (a := a) (V ++ ws) y
  | label ws n cont y hb => simpa using TT.label (V ++ ws) n cont y hb
  | frame ws n fi y hb => simpa using TT.frame (V ++ ws) n fi y hb

/-! ## Concatenation -/

/-- **The relation is closed under concatenation.** -/
theorem R.append {fw tl : Bool} {x' y' : List Admin} (h' : R fw tl x' y') :
    ∀ {x y : List Admin}, R fw tl x y → R fw tl (x ++ x') (y ++ y')
  | _, _, .nil => by simpa using h'
  | _, _, .same ha h => by simpa using R.same ha (R.append h' h)
  | _, _, .instr h => by simpa using R.instr (R.append h' h)
  | _, _, .rcr hc h => by simpa using R.rcr hc (R.append h' h)
  | _, _, .label hc hb h => by simpa using R.label hc hb (R.append h' h)
  | _, _, .handler hb h => by simpa using R.handler hb (R.append h' h)
  | _, _, .callee hce h => by simpa using R.callee hce (R.append h' h)
  | _, _, .bub U X hp => by simpa using R.bub U (X ++ x') (PTL.append hp y')
  | _, _, .trapC us x ht => by simpa using R.trapC (fw := fw) (tl := tl) us (x ++ x') (TA.append ht y')
  | _, _, .throwC us x ht => by
    simpa using R.throwC (fw := fw) (tl := tl) us (x ++ x') (TT.append ht y')

/-- Value prefixes. -/
theorem R.valPre {fw tl : Bool} {x y : List Admin} (h : R fw tl x y) :
    ∀ V : List Val, R fw tl (vals V ++ x) (vals V ++ y)
  | [] => by simpa [Sim.vals_nil'] using h
  | v :: V => by
    rw [Sim.vals_cons', List.cons_append, List.cons_append]
    exact .same (Val.toAdmin_not_ctx v) (R.valPre h V)

/-- **Identical code followed by related code.** -/
theorem R.refl_append {fw tl : Bool} {x y : List Admin} (h : R fw tl x y) (z : List Admin) :
    R fw tl (z ++ x) (z ++ y) :=
  R.append h (R.refl fw tl z)

end Silmaril.Raw.Wasm.LimeCompile.TailSim
