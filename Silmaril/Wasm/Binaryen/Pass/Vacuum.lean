module

public import Silmaril.Wasm.Binaryen.Effects
public import Silmaril.Wasm.Binaryen.Uniform
public import Silmaril.Wasm.Binaryen.SeqTyping
public import Silmaril.Wasm.Binaryen.CtxRefines
public import Silmaril.Wasm.Binaryen.StraightLine
public import Silmaril.Wasm.Binaryen.LoopCex
public import Silmaril.Wasm.Binaryen.TrapCex
public import Silmaril.Wasm.Execution.Core.Properties

@[expose] public section

/-! # P2: Vacuum-lite

Binaryen's `Vacuum` (`src/passes/Vacuum.cpp`, version_133) removes code with no
effect. The lite version, bottom-up:

* `nop` is removed;
* `drop e` is removed when `e` is self-contained (`scType`: an integer constant or
  operator tree whose operands are all children) and removable (`Effects.removable`);
* `if c {} {}` becomes `drop c`.

With `trapsNeverHappen` (`tnh = true`) two more rewrites apply, both sound only
against `TrapsUB`:

* `Vacuum.cpp:180` (`visitBlock`): code heading to an `unreachable` is removed,
  scanning backwards and stopping at anything that may branch away, call, not
  return, or initialise a local (`trimToTrap`);
* `Vacuum.cpp:303` (`visitIf`): an `if` one of whose arms is `unreachable`
  becomes `drop c` followed by the other arm, kept in a `block` so its branch
  depths do not change.

`vacuum_sound` is an equivalence; `vacuum_tnh_sound` is `SeqRefines TrapsUB`.

**Proof structure.** Typing (`vacuum_typed`) is a `TyRepl` chain (`SeqTyping.lean`):
every rewrite is typed wherever its source is, in well-formed contexts. Soundness
composes local rewrites (`VEq`/`VTnh`, `CtxRefines.lean`) through one-hole contexts;
each local rewrite comes from a bridge of `Joinable.lean` applied at the typing of the
hole read off the plugged module. The local runs: self-contained trees evaluate to one
constant or trap (`sc_eval`); `trimToTrap`'s removed code is straight-line and reaches
the `unreachable` or traps (`StraightLine.lean`, `heads_run_trap`).

**Flagged changes** (each with its counterexample): the `drop` rule's `scType` guard
and `headsToTrap`'s local-write exclusion (`vacuum_typed_false_v0`,
`vacuum_typed_false_v0_tnh`: the first-stated pass broke typing); `block_unwrap` now
excludes loops and calls (`block_unwrap_false_v0`: a diverging body never joins); the
typing and soundness theorems assume a well-formed context. `vacuum_tnh_not_equiv` is
proved on a concrete module whose start function traps (`TrapCex.lean`).

**Scope.** This module does not establish the legacy general results the soundness theorems
`vacuum_sound`, `vacuum_tnh_sound` and their local lemmas (`veq_*`, `vtnh_*`, `vac*_veq`,
`vac*_tnh`, `trim_tnh*`). The toolkit contracts are supplied by separate proof modules.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Validation Numerics

/-- Is this tree the `unreachable` instruction? -/
def isUnreachable : BExpr → Bool
  | .op .unreachable [] => true
  | _ => false

/-- An arm consisting of a single `unreachable`. -/
def unreachableArm : List BExpr → Bool
  | [e] => isUnreachable e
  | _ => false

/-- Code that keeps heading to a trap (`!transfersControlFlow && !calls &&
!mayNotReturn`, `Vacuum.cpp:196`), and initialises no local. -/
-- FLAG(statement-change): `f.localsWritten.isEmpty` added. Removing a `local.set` before
-- an `unreachable` breaks Core 3.0 typing when the set initialises a non-defaultable
-- local that the block's type claims (`vacuum_typed_false_v0`, case `tnh = true`).
def headsToTrap (e : BExpr) : Bool :=
  let f := effects e
  f.localsWritten.isEmpty && !f.any && !f.branchesOut && f.breakTargets.isEmpty && !f.calls &&
    !f.mayNotReturn

/-- Remove code heading to an `unreachable` (`trapsNeverHappen` only). -/
def trimToTrap (es : List BExpr) : List BExpr :=
  (es.foldr (fun e (acc : List BExpr × Bool) =>
    if isUnreachable e then (e :: acc.1, true)
    else if acc.2 && headsToTrap e then (acc.1, true)
    else (e :: acc.1, false)) ([], false)).1

/-- The result type of a **self-contained** integer tree: a constant, or an integer
operator applied to exactly as many self-contained operands of the right type as it
consumes. Such a tree pushes exactly one value and reads nothing else (Binaryen's IR
is always folded this way; layer D also allows stacky trees, whose removal would
change the stack). -/
def scType : BExpr → Option IntType
  | .op (.intConst t _) [] => some t
  | .op (.intUnOp t op) [a] => if op.valid t && scType a == some t then some t else none
  | .op (.intBinOp t _) [a, b] =>
      if scType a == some t && scType b == some t then some t else none
  | .op (.intTestOp t _) [a] => if scType a == some t then some .i32 else none
  | .op (.intRelOp t _) [a, b] =>
      if scType a == some t && scType b == some t then some .i32 else none
  | _ => none

/-- Vacuum one operator node. -/
-- FLAG(statement-change): the `drop` rule now also requires the dropped tree to be
-- self-contained (`scType`). Without it, `drop (i32.add)` with stack operands, or
-- (with `tnh`) `drop unreachable`, is removed and the result is ill typed
-- (`vacuum_typed_false_v0`).
def vacuumOp (tnh : Bool) (i : Instr) (args : List BExpr) : List BExpr :=
  match i, args with
  | .nop, [] => []
  | .drop, [e] => if (scType e).isSome && (effects e).removable tnh then [] else [.op .drop [e]]
  | _, _ => [.op i args]

/-- Vacuum one `if`. -/
def vacuumIf (tnh : Bool) (bt : BlockType) (c t e : List BExpr) : List BExpr :=
  match bt, t, e with
  | .empty, [], [] => [.op .drop c]
  | _, _, _ =>
    if tnh && unreachableArm t && !unreachableArm e then [.op .drop c, .block bt e]
    else if tnh && unreachableArm e && !unreachableArm t then [.op .drop c, .block bt t]
    else [.if_ bt c t e]

/-- Apply `trimToTrap` only under `trapsNeverHappen`. -/
def trimIf (tnh : Bool) (es : List BExpr) : List BExpr := if tnh then trimToTrap es else es

mutual
/-- Vacuum a tree; the result is spliced into the enclosing list. -/
def vacE (tnh : Bool) : BExpr → List BExpr
  | .op i args => vacuumOp tnh i (vacL tnh args)
  | .block bt b => [.block bt (trimIf tnh (vacL tnh b))]
  | .loop bt b => [.loop bt (trimIf tnh (vacL tnh b))]
  | .if_ bt c t e =>
      vacuumIf tnh bt (vacL tnh c) (trimIf tnh (vacL tnh t)) (trimIf tnh (vacL tnh e))
  | .tryTable bt cs b => [.tryTable bt cs (vacL tnh b)]
/-- Vacuum a list. -/
def vacL (tnh : Bool) : List BExpr → List BExpr
  | [] => []
  | e :: es => vacE tnh e ++ vacL tnh es
end

/-- The pass on a function body. -/
def vacuum (tnh : Bool) (es : List BExpr) : List BExpr := trimIf tnh (vacL tnh es)

/-- The pass on a module. -/
def vacuumModule (tnh : Bool) (m : BModule) : BModule := m.mapBodies (vacuum tnh)

/-! ## Typing -/

section Typing

theorem intConst_typing {C : Context} {it : InstrType} {t : IntType} {b : BitVec t.width}
    (h : InstrOk C (.intConst t b) it) : it = .plain [] [.num (.int t)] := by
  cases h with
  | numeric h => cases h; rfl
  | _ => rename_i h; cases h

theorem resultOk_num {C : Context} (ts : List IntType) :
    ResultOk C.toTypeCtx (ts.map fun t => (.num (.int t) : CValType)) := by
  intro t ht
  obtain ⟨u, -, rfl⟩ := List.mem_map.mp ht
  exact TyOk.num' (t := .int u)

theorem drop_typed {C : Context} (t : IntType) :
    InstrsOk C [.drop] (.plain [.num (.int t)] []) :=
  .instr (.parametric (.drop (TyOk.num' (t := .int t))))

theorem const_typed {C : Context} (t : IntType) (b : BitVec t.width) :
    InstrsOk C [.intConst t b] (.plain [] [.num (.int t)]) :=
  .instr (.numeric (.intConst t b))

/-- Frame a plain typing by a valid stack. -/
theorem frame_plain {C : Context} {is : List Instr} {ts t₁ t₂ : List CValType}
    (h : InstrsOk C is (.plain t₁ t₂)) (hok : ResultOk C.toTypeCtx ts) :
    InstrsOk C is (.plain (ts ++ t₁) (ts ++ t₂)) := .frame h hok

theorem tyRepl_const (t : IntType) (b : BitVec t.width) :
    TyRepl [.intConst t b] [.intConst t 0] :=
  TyRepl.of_instr fun _ _ _ hi => by rw [intConst_typing hi]; exact const_typed t 0

theorem tyRepl_unop (t : IntType) (op : IntUnOp) : TyRepl [.intUnOp t op] [] :=
  TyRepl.of_instr fun C _ _ hi => by
    cases hi with
    | numeric h => cases h; exact InstrsOk.id (ts := [.num (.int t)]) (by simp)
    | _ => rename_i h; cases h

theorem tyRepl_binop (t : IntType) (op : IntBinOp) : TyRepl [.intBinOp t op] [.drop] :=
  TyRepl.of_instr fun C _ _ hi => by
    cases hi with
    | numeric h =>
      cases h
      exact frame_plain (ts := [.num (.int t)]) (drop_typed (C := C) t) (by simp)
    | _ => rename_i h; cases h

theorem tyRepl_testop (t : IntType) (op : IntTestOp) :
    TyRepl [.intTestOp t op] [.drop, .intConst .i32 0] :=
  TyRepl.of_instr fun C _ _ hi => by
    cases hi with
    | numeric h =>
      cases h
      exact InstrsOk.cons (.parametric (.drop (TyOk.num' (t := .int t)))) (by simp)
        (const_typed .i32 0)
    | _ => rename_i h; cases h

theorem tyRepl_relop (t : IntType) (op : IntRelOp) :
    TyRepl [.intRelOp t op] [.drop, .drop, .intConst .i32 0] :=
  TyRepl.of_instr fun C _ _ hi => by
    cases hi with
    | numeric h =>
      cases h
      have h₁ : InstrsOk C [.drop] (.plain [.num (.int t), .num (.int t)] [.num (.int t)]) :=
        frame_plain (ts := [.num (.int t)]) (drop_typed (C := C) t) (by simp)
      have h₂ : InstrsOk C [.drop, .intConst .i32 0] (.plain [.num (.int t)] [.i32]) :=
        InstrsOk.cons (.parametric (.drop (TyOk.num' (t := .int t)))) (by simp)
          (const_typed .i32 0)
      simpa using InstrsOk.seq h₁ (by simp) h₂
    | _ => rename_i h; cases h

/-- `const; drop` is the identity (in every typing). -/
theorem tyRepl_const_drop (t : IntType) (b : BitVec t.width) :
    TyRepl [.intConst t b, .drop] [] := by
  intro C it hC hX
  obtain ⟨m, xs₁, xs₂, h₁, h₂, hL⟩ := InstrsOk.split (is₁ := [.intConst t b]) (is₂ := [.drop])
    hC hX rfl
  have hreg := InstrsOk.regular hC hX
  have r₁ := InstrsOk.regular hC h₁
  obtain ⟨ts₁, it₁, hts₁, hi₁, hs₁⟩ := single_inv' hC h₁
  rw [intConst_typing hi₁] at hs₁
  have hx₁ : ∀ x ∈ xs₁, ∃ t, C.locals[x]? = some ⟨.set, t⟩ := fun x hx => hs₁.2.2 x hx (by simp)
  have hC₁ : C.initLocals xs₁ = C := Context.initLocals_of_set hx₁
  rw [hC₁] at h₂
  obtain ⟨ts₂, it₂, hts₂, hi₂, hs₂⟩ := single_inv' hC h₂
  cases hi₂ with
  | parametric h =>
    cases h with
    | drop ht =>
      rename_i u
      have hx₂ : ∀ x ∈ xs₂, ∃ t, C.locals[x]? = some ⟨.set, t⟩ :=
        fun x hx => hs₂.2.2 x hx (by simp)
      have hm : ResultSub C.toTypeCtx (ts₁ ++ [.num (.int t)]) (ts₂ ++ [u]) :=
        ResultSub.trans hC.types r₁.2.1 hs₁.2.1 hs₂.1
      have hl := resultSub_length hm
      simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hl
      have h12 := (resultSub_append_inv hm hl).1
      have hp : ResultSub C.toTypeCtx it.params it.results :=
        ResultSub.trans hC.types hts₁ (by simpa using hs₁.1)
          (ResultSub.trans hC.types hts₂ h12 (by simpa using hs₂.2.1))
      exact nil_typed (xs := it.inits) (p := it.params) (r := it.results) hreg hp
        (inits_set_of_split hreg hL (by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          exacts [hx₁ x hx, hx₂ x hx]))
  | _ => rename_i h; cases h

theorem isUnreachable_eq {e : BExpr} (h : isUnreachable e = true) : e = .op .unreachable [] := by
  match e, h with
  | .op .unreachable [], _ => rfl

theorem unreachableArm_eq {es : List BExpr} (h : unreachableArm es = true) :
    es = [.op .unreachable []] := by
  match es, h with
  | [e], h => rw [isUnreachable_eq h]

/-- Self-contained trees type like a constant. -/
theorem tyRepl_sc : ∀ (e : BExpr) {t : IntType}, scType e = some t →
    TyRepl e.lower [.intConst t 0]
  | .op (.intConst t' b) [], t, h => by
      simp only [scType, Option.some.injEq] at h
      subst h
      simpa using tyRepl_const t' b
  | .op (.intUnOp t' op) [a], t, h => by
      simp only [scType] at h
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        simp only [Option.some.injEq] at h
        subst h
        have ha := tyRepl_sc a hc.2
        have : TyRepl (a.lower ++ [.intUnOp t' op]) ([.intConst t' 0] ++ []) :=
          TyRepl.append ha (tyRepl_unop t' op)
        simpa using this
      · cases h
  | .op (.intBinOp t' op) [a, b], t, h => by
      simp only [scType] at h
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        simp only [Option.some.injEq] at h
        subst h
        have h₁ : TyRepl (a.lower ++ (b.lower ++ [.intBinOp t' op]))
            ([.intConst t' 0] ++ ([.intConst t' 0] ++ [.drop])) :=
          TyRepl.append (tyRepl_sc a hc.1) (TyRepl.append (tyRepl_sc b hc.2) (tyRepl_binop t' op))
        have h₂ : TyRepl ([.intConst t' 0] ++ ([.intConst t' 0] ++ [.drop]))
            ([.intConst t' 0] ++ []) :=
          TyRepl.append_left _ (tyRepl_const_drop t' 0)
        simpa [List.append_assoc] using h₁.trans h₂
      · cases h
  | .op (.intTestOp t' op) [a], t, h => by
      simp only [scType] at h
      split at h
      · next hc =>
        simp only [beq_iff_eq] at hc
        simp only [Option.some.injEq] at h
        subst h
        have h₁ : TyRepl (a.lower ++ [.intTestOp t' op])
            ([.intConst t' 0] ++ [.drop, .intConst .i32 0]) :=
          TyRepl.append (tyRepl_sc a hc) (tyRepl_testop t' op)
        have h₂ : TyRepl ([.intConst t' 0, .drop] ++ [.intConst .i32 0])
            ([] ++ [.intConst .i32 0]) :=
          TyRepl.append_right (tyRepl_const_drop t' 0) _
        simpa using h₁.trans h₂
      · cases h
  | .op (.intRelOp t' op) [a, b], t, h => by
      simp only [scType] at h
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        simp only [Option.some.injEq] at h
        subst h
        have h₁ : TyRepl (a.lower ++ (b.lower ++ [.intRelOp t' op]))
            ([.intConst t' 0] ++ ([.intConst t' 0] ++ [.drop, .drop, .intConst .i32 0])) :=
          TyRepl.append (tyRepl_sc a hc.1) (TyRepl.append (tyRepl_sc b hc.2) (tyRepl_relop t' op))
        have h₂ : TyRepl
            ([.intConst t' 0] ++ ([.intConst t' 0, .drop] ++ [.drop, .intConst .i32 0]))
            ([.intConst t' 0] ++ ([] ++ [.drop, .intConst .i32 0])) :=
          TyRepl.append_left _ (TyRepl.append_right (tyRepl_const_drop t' 0) _)
        have h₃ : TyRepl ([.intConst t' 0, .drop] ++ [.intConst .i32 0])
            ([] ++ [.intConst .i32 0]) :=
          TyRepl.append_right (tyRepl_const_drop t' 0) _
        simpa [List.append_assoc] using (h₁.trans h₂).trans h₃
      · cases h

/-- Removing a dropped self-contained tree. -/
theorem tyRepl_drop_sc {e : BExpr} {t : IntType} (h : scType e = some t) :
    TyRepl (e.lower ++ [.drop]) [] :=
  (TyRepl.append_right (tyRepl_sc e h) _).trans (tyRepl_const_drop t 0)

theorem tyRepl_nop : TyRepl [.nop] [] :=
  TyRepl.of_instr fun _ _ _ hi => by
    cases hi with
    | parametric h => cases h; exact .nil
    | _ => rename_i h; cases h

theorem tyRepl_if_empty (b₁ b₂ : List Instr) : TyRepl [.if_ .empty b₁ b₂] [.drop] :=
  TyRepl.of_instr fun _ _ _ hi => by
    cases hi with
    | if_ hbt _ _ => cases hbt; exact drop_typed .i32
    | _ => rename_i h; cases h

/-- The TNH `if` rule, unreachable `then` arm. -/
theorem tyRepl_if_unr_then (bt : BlockType) (b₂ : List Instr) :
    TyRepl [.if_ bt [.unreachable] b₂] [.drop, .block bt b₂] :=
  TyRepl.of_instr fun C _ hC hi => by
    cases hi with
    | @if_ _ _ _ _ t₁ t₂ _ _ hbt _ h₂ =>
      have hd : InstrsOk C [.drop] (.plain (t₁ ++ [.i32]) t₁) := by
        simpa [Ty.i32] using frame_plain (drop_typed (C := C) .i32) (hbt.regular hC).1
      have hb : InstrsOk C [.block bt b₂] (.plain t₁ t₂) := .instr (.block hbt h₂)
      simpa using InstrsOk.seq hd (by simp) hb
    | _ => rename_i h; cases h

/-- The TNH `if` rule, unreachable `else` arm. -/
theorem tyRepl_if_unr_else (bt : BlockType) (b₁ : List Instr) :
    TyRepl [.if_ bt b₁ [.unreachable]] [.drop, .block bt b₁] :=
  TyRepl.of_instr fun C _ hC hi => by
    cases hi with
    | @if_ _ _ _ _ t₁ t₂ _ _ hbt h₁ _ =>
      have hd : InstrsOk C [.drop] (.plain (t₁ ++ [.i32]) t₁) := by
        simpa [Ty.i32] using frame_plain (drop_typed (C := C) .i32) (hbt.regular hC).1
      have hb : InstrsOk C [.block bt b₁] (.plain t₁ t₂) := .instr (.block hbt h₁)
      simpa using InstrsOk.seq hd (by simp) hb
    | _ => rename_i h; cases h

/-- Code initialising no local, followed by `unreachable`, types like `unreachable`. -/
theorem tyRepl_cut {X : List Instr} (hX : ∀ i ∈ X, initsLocal i = false) :
    TyRepl (X ++ [.unreachable]) [.unreachable] := by
  intro C it hC h
  obtain ⟨m, xs₁, xs₂, h₁, h₂, hL⟩ := InstrsOk.split hC h rfl
  have hreg := InstrsOk.regular hC h
  have hx₁ := InstrsOk.inits_set h₁ hX
  rw [Context.initLocals_of_set hx₁] at h₂
  have hx₂ := InstrsOk.inits_set h₂ (by simp [initsLocal])
  have hu : InstrsOk C [.unreachable] (.plain it.params it.results) :=
    .instr (.parametric (.unreachable ⟨hreg.1, hreg.2.1, by simp⟩))
  refine .sub hu ⟨ResultSub.refl _ _, ResultSub.refl _ _, fun x hx _ => ?_⟩ hreg
  exact inits_set_of_split hreg hL (by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    exacts [hx₁ x hx, hx₂ x hx]) x hx

mutual
/-- Code that writes no local and stays in the analysed fragment initialises no local. -/
theorem lower_noInit : ∀ (e : BExpr), (effects e).any = false →
    (effects e).localsWritten = [] → ∀ i ∈ e.lower, initsLocal i = false
  | .op i args, ha, hw => by
      simp only [effects, Effects.merge, Bool.or_eq_false_iff, List.append_eq_nil_iff] at ha hw
      intro j hj
      simp only [BExpr.lower_op, List.mem_append, List.mem_singleton] at hj
      rcases hj with hj | rfl
      · exact lowerList_noInit args ha.1 hw.1 j hj
      · cases j <;> simp_all [instrEffects, initsLocal]
  | .block _ _, _, _ => by intro j hj; simp [BExpr.lower] at hj; subst hj; rfl
  | .loop _ _, _, _ => by intro j hj; simp [BExpr.lower] at hj; subst hj; rfl
  | .if_ _ c _ _, ha, hw => by
      simp only [effects, Effects.merge, Bool.or_eq_false_iff, List.append_eq_nil_iff] at ha hw
      intro j hj
      simp only [BExpr.lower, List.mem_append, List.mem_singleton] at hj
      rcases hj with hj | rfl
      · exact lowerList_noInit c ha.1 hw.1 j hj
      · rfl
  | .tryTable _ _ _, _, _ => by intro j hj; simp [BExpr.lower] at hj; subst hj; rfl
theorem lowerList_noInit : ∀ (es : List BExpr), (effectsList es).any = false →
    (effectsList es).localsWritten = [] → ∀ i ∈ BExpr.lowerList es, initsLocal i = false
  | [], _, _ => by simp
  | e :: es, ha, hw => by
      simp only [effectsList, Effects.merge, Bool.or_eq_false_iff, List.append_eq_nil_iff] at ha hw
      intro j hj
      simp only [BExpr.lowerList_cons, List.mem_append] at hj
      rcases hj with hj | hj
      · exact lower_noInit e ha.1 hw.1 j hj
      · exact lowerList_noInit es ha.2 hw.2 j hj
end

theorem headsToTrap_noInit {e : BExpr} (h : headsToTrap e = true) :
    ∀ i ∈ e.lower, initsLocal i = false := by
  simp only [headsToTrap, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact lower_noInit e (by simpa using h2) (by simpa using h1)

/-- One step of `trimToTrap`. -/
def trimStep (e : BExpr) (acc : List BExpr × Bool) : List BExpr × Bool :=
  if isUnreachable e then (e :: acc.1, true)
  else if acc.2 && headsToTrap e then (acc.1, true)
  else (e :: acc.1, false)

theorem trimToTrap_eq (es : List BExpr) :
    trimToTrap es = (es.foldr trimStep ([], false)).1 := rfl

theorem trim_typed_aux : ∀ es : List BExpr,
    TyRepl (BExpr.lowerList es) (BExpr.lowerList (es.foldr trimStep ([], false)).1) ∧
      ((es.foldr trimStep ([], false)).2 = true →
        ∃ rest, (es.foldr trimStep ([], false)).1 = .op .unreachable [] :: rest)
  | [] => ⟨TyRepl.refl _, by simp⟩
  | e :: es => by
      obtain ⟨ih, hflag⟩ := trim_typed_aux es
      simp only [List.foldr_cons]
      generalize es.foldr trimStep ([], false) = acc at ih hflag
      unfold trimStep
      split
      · next hu =>
        refine ⟨by simpa using TyRepl.append_left e.lower ih, fun _ => ⟨acc.1, ?_⟩⟩
        rw [isUnreachable_eq hu]
      · split
        · next hu hc =>
          simp only [Bool.and_eq_true] at hc
          obtain ⟨rest, hr⟩ := hflag hc.1
          refine ⟨?_, fun _ => ⟨rest, hr⟩⟩
          rw [hr] at ih ⊢
          have h₁ : TyRepl (e.lower ++ BExpr.lowerList es)
              (e.lower ++ ([.unreachable] ++ BExpr.lowerList rest)) := by
            simpa using TyRepl.append_left e.lower ih
          have h₂ : TyRepl ((e.lower ++ [.unreachable]) ++ BExpr.lowerList rest)
              ([.unreachable] ++ BExpr.lowerList rest) :=
            TyRepl.append_right (tyRepl_cut (headsToTrap_noInit hc.2)) _
          simpa [List.append_assoc] using h₁.trans (by simpa [List.append_assoc] using h₂)
        · exact ⟨by simpa using TyRepl.append_left e.lower ih, by simp⟩

theorem trim_typed (es : List BExpr) :
    TyRepl (BExpr.lowerList es) (BExpr.lowerList (trimToTrap es)) :=
  (trim_typed_aux es).1

theorem trimIf_typed (tnh : Bool) (es : List BExpr) :
    TyRepl (BExpr.lowerList es) (BExpr.lowerList (trimIf tnh es)) := by
  cases tnh
  · exact TyRepl.refl _
  · exact trim_typed es

theorem vacuumOp_typed (tnh : Bool) (i : Instr) (args : List BExpr) :
    TyRepl (BExpr.lowerList args ++ [i]) (BExpr.lowerList (vacuumOp tnh i args)) := by
  unfold vacuumOp
  split
  · simpa using tyRepl_nop
  · next e =>
    split
    · next hc =>
      simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hc
      obtain ⟨⟨t, ht⟩, -⟩ := hc
      simpa using tyRepl_drop_sc ht
    · simpa using TyRepl.refl _
  · simpa using TyRepl.refl _

theorem vacuumIf_typed (tnh : Bool) (bt : BlockType) (c t e : List BExpr) :
    TyRepl (BExpr.lowerList c ++ [.if_ bt (BExpr.lowerList t) (BExpr.lowerList e)])
      (BExpr.lowerList (vacuumIf tnh bt c t e)) := by
  unfold vacuumIf
  split
  · simpa using TyRepl.append_left (BExpr.lowerList c) (tyRepl_if_empty [] [])
  · split
    · next h =>
      simp only [Bool.and_eq_true] at h
      rw [unreachableArm_eq h.1.2]
      simpa [BExpr.lower] using
        TyRepl.append_left (BExpr.lowerList c) (tyRepl_if_unr_then bt (BExpr.lowerList e))
    · split
      · next h =>
        simp only [Bool.and_eq_true] at h
        rw [unreachableArm_eq h.1.2]
        simpa [BExpr.lower] using
          TyRepl.append_left (BExpr.lowerList c) (tyRepl_if_unr_else bt (BExpr.lowerList t))
      · simpa [BExpr.lower] using TyRepl.refl _

mutual
theorem vacE_typed (tnh : Bool) : ∀ e : BExpr, TyRepl e.lower (BExpr.lowerList (vacE tnh e))
  | .op i args => by
      simp only [vacE, BExpr.lower_op]
      exact (TyRepl.append_right (vacL_typed tnh args) _).trans (vacuumOp_typed tnh i _)
  | .block bt b => by
      simpa [vacE, BExpr.lower] using
        TyRepl.block ((vacL_typed tnh b).trans (trimIf_typed tnh _)) bt
  | .loop bt b => by
      simpa [vacE, BExpr.lower] using
        TyRepl.loop ((vacL_typed tnh b).trans (trimIf_typed tnh _)) bt
  | .if_ bt c t e => by
      simp only [vacE]
      have h₁ := TyRepl.append (vacL_typed tnh c)
        (TyRepl.if_ ((vacL_typed tnh t).trans (trimIf_typed tnh _))
          ((vacL_typed tnh e).trans (trimIf_typed tnh _)) bt)
      exact (by simpa [BExpr.lower] using h₁ : TyRepl (BExpr.if_ bt c t e).lower _).trans
        (vacuumIf_typed tnh bt _ _ _)
  | .tryTable bt cs b => by
      simpa [vacE, BExpr.lower] using TyRepl.tryTable (vacL_typed tnh b) bt cs
theorem vacL_typed (tnh : Bool) : ∀ es : List BExpr,
    TyRepl (BExpr.lowerList es) (BExpr.lowerList (vacL tnh es))
  | [] => by simpa [vacL] using TyRepl.refl []
  | e :: es => by
      simpa [vacL] using TyRepl.append (vacE_typed tnh e) (vacL_typed tnh es)
end

end Typing

/-! ## The pre-flag pass is not type-preserving

The pass as first stated (an unguarded `drop` rule and a `headsToTrap` that allowed
local writes) breaks typing, even in well-formed contexts. -/

namespace VacuumV0

/-- `headsToTrap` before the flag. -/
def headsToTrap₀ (e : BExpr) : Bool :=
  let f := effects e
  !f.any && !f.branchesOut && f.breakTargets.isEmpty && !f.calls && !f.mayNotReturn

/-- `trimToTrap` before the flag. -/
def trimToTrap₀ (es : List BExpr) : List BExpr :=
  (es.foldr (fun e (acc : List BExpr × Bool) =>
    if isUnreachable e then (e :: acc.1, true)
    else if acc.2 && headsToTrap₀ e then (acc.1, true)
    else (e :: acc.1, false)) ([], false)).1

/-- `vacuumOp` before the flag. -/
def vacuumOp₀ (tnh : Bool) (i : Instr) (args : List BExpr) : List BExpr :=
  match i, args with
  | .nop, [] => []
  | .drop, [e] => if (effects e).removable tnh then [] else [.op .drop [e]]
  | _, _ => [.op i args]

/-- `trimIf` before the flag. -/
def trimIf₀ (tnh : Bool) (es : List BExpr) : List BExpr := if tnh then trimToTrap₀ es else es

mutual
/-- `vacE` before the flag. -/
def vacE₀ (tnh : Bool) : BExpr → List BExpr
  | .op i args => vacuumOp₀ tnh i (vacL₀ tnh args)
  | .block bt b => [.block bt (trimIf₀ tnh (vacL₀ tnh b))]
  | .loop bt b => [.loop bt (trimIf₀ tnh (vacL₀ tnh b))]
  | .if_ bt c t e =>
      vacuumIf tnh bt (vacL₀ tnh c) (trimIf₀ tnh (vacL₀ tnh t)) (trimIf₀ tnh (vacL₀ tnh e))
  | .tryTable bt cs b => [.tryTable bt cs (vacL₀ tnh b)]
/-- `vacL` before the flag. -/
def vacL₀ (tnh : Bool) : List BExpr → List BExpr
  | [] => []
  | e :: es => vacE₀ tnh e ++ vacL₀ tnh es
end

/-- The pass before the flag. -/
def vacuum₀ (tnh : Bool) (es : List BExpr) : List BExpr := trimIf₀ tnh (vacL₀ tnh es)

end VacuumV0

theorem emptyCtx_wf : ({} : Context).Wf :=
  ⟨by simp [TypeCtx.Ok], by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩

/-- One unset `i32` local. -/
def unsetCtx : Context := { locals := [⟨.unset, .num (.int .i32)⟩] }

theorem unsetCtx_wf : unsetCtx.Wf :=
  ⟨by simp [TypeCtx.Ok, unsetCtx], by simp [unsetCtx], by simp [unsetCtx], by simp [unsetCtx],
    by simp [unsetCtx], by simp [unsetCtx, TyOk.num'], by simp [unsetCtx], by simp [unsetCtx],
    by simp [unsetCtx]⟩

/-- `i32.const 1; i32.const 2; drop (i32.add)` with the operands on the stack. -/
def stackyDrop : List BExpr :=
  [.op (.intConst .i32 1) [], .op (.intConst .i32 2) [],
    .op .drop [.op (.intBinOp .i32 .add) []]]

/-- `local.set 0 (i32.const 1); unreachable` for an unset local. -/
def setBeforeTrap : List BExpr :=
  [.op (.localSet ⟨⟨0, by decide⟩⟩) [.op (.intConst .i32 1) []], .op .unreachable []]

theorem stackyDrop_typed : SeqOk {} stackyDrop (.plain [] []) := by
  show InstrsOk {} [.intConst .i32 1, .intConst .i32 2, .intBinOp .i32 .add, .drop] _
  have h₁ : InstrsOk ({} : Context) [.intConst .i32 2, .intBinOp .i32 .add, .drop]
      (.plain [.num (.int .i32)] []) := by
    have hc : InstrsOk ({} : Context) [.intConst .i32 2]
        (.plain [.num (.int .i32)] [.num (.int .i32), .num (.int .i32)]) := by
      exact frame_plain (ts := [.num (.int .i32)]) (const_typed (C := {}) .i32 2) (by simp)
    have ha : InstrsOk ({} : Context) [.intBinOp .i32 .add, .drop]
        (.plain [.num (.int .i32), .num (.int .i32)] []) :=
      InstrsOk.cons (.numeric (.intBinOp .i32 .add)) (by simp) (drop_typed .i32)
    simpa using InstrsOk.seq hc (by simp) ha
  exact InstrsOk.cons (.numeric (.intConst .i32 1)) (by simp) h₁

theorem stackyDrop_vacuum₀ : VacuumV0.vacuum₀ false stackyDrop =
    [.op (.intConst .i32 1) [], .op (.intConst .i32 2) []] := rfl

theorem two_consts_untyped :
    ¬ SeqOk {} [.op (.intConst .i32 1) [], .op (.intConst .i32 2) []] (.plain [] []) := by
  intro h
  change InstrsOk {} ([.intConst .i32 1] ++ [.intConst .i32 2]) _ at h
  obtain ⟨m, xs₁, xs₂, -, h₂, -⟩ := InstrsOk.split emptyCtx_wf h rfl
  obtain ⟨ts, it₀, -, hi, hs⟩ := single_inv' (emptyCtx_wf.initLocals _) h₂
  rw [intConst_typing hi] at hs
  have := resultSub_length hs.2.1
  simp at this

theorem setBeforeTrap_typed : SeqOk unsetCtx setBeforeTrap ⟨[], [0], []⟩ := by
  show InstrsOk unsetCtx [.intConst .i32 1, .localSet ⟨⟨0, by decide⟩⟩, .unreachable] _
  have hu : InstrsOk (unsetCtx.initLocals [0]) [.unreachable] (.plain [] []) :=
    .instr (.parametric (.unreachable ⟨by simp [ResultOk], by simp [ResultOk], by simp⟩))
  have hs : InstrsOk unsetCtx [.localSet ⟨⟨0, by decide⟩⟩, .unreachable]
      ⟨[.num (.int .i32)], [0] ++ [], []⟩ :=
    InstrsOk.cons (.variable (.localSet (i := .unset) rfl)) (by simp [unsetCtx]) hu
  exact InstrsOk.cons (xs₁ := []) (.numeric (.intConst .i32 1)) (by simp) hs

theorem setBeforeTrap_vacuum₀ :
    VacuumV0.vacuum₀ true setBeforeTrap = [.op .unreachable []] := rfl

theorem unreachable_untyped_unset : ¬ SeqOk unsetCtx [.op .unreachable []] ⟨[], [0], []⟩ := by
  intro h
  change InstrsOk unsetCtx [.unreachable] _ at h
  obtain ⟨ts, it₀, -, hi, hs⟩ := single_inv' unsetCtx_wf h
  have h0 := InstrOk.inits_nil hi rfl
  obtain ⟨t, ht⟩ := hs.2.2 0 (by simp) (by simp [h0])
  simp [unsetCtx] at ht

/-- **The pass as first stated was not type-preserving** without TNH, even in
well-formed contexts: a `drop` of a stacky tree is removed. Hence the flagged
`scType` guard. -/
theorem vacuum_typed_false_v0 :
    ¬ ∀ (tnh : Bool) (C : Context) (it : InstrType) (es : List BExpr), C.Wf → SeqOk C es it →
      SeqOk C (VacuumV0.vacuum₀ tnh es) it := by
  intro h
  have := h false {} _ _ emptyCtx_wf stackyDrop_typed
  rw [stackyDrop_vacuum₀] at this
  exact two_consts_untyped this

/-- **The pass as first stated was not type-preserving** with TNH either: a
`local.set` initialising a local before an `unreachable` is removed. Hence the
flagged `headsToTrap` change. -/
theorem vacuum_typed_false_v0_tnh :
    ¬ ∀ (C : Context) (it : InstrType) (es : List BExpr), C.Wf → SeqOk C es it →
      SeqOk C (VacuumV0.vacuum₀ true es) it := by
  intro h
  have := h unsetCtx _ _ unsetCtx_wf setBeforeTrap_typed
  rw [setBeforeTrap_vacuum₀] at this
  exact unreachable_untyped_unset this

/-- Vacuum preserves typing. -/
-- FLAG(statement-change): hypothesis `hC : C.Wf` added (typing inversion through
-- `InstrsOk.split` needs a well-formed context; every function body is typed in one).
theorem vacuum_typed {tnh : Bool} {C : Context} {it : InstrType} {es : List BExpr}
    (hC : C.Wf) (h : SeqOk C es it) : SeqOk C (vacuum tnh es) it :=
  ((vacL_typed tnh es).trans (trimIf_typed tnh _)) C it hC h

/-! ## Semantics: running the local rewrites -/

section Run

variable {P : Profile} {H : Type}

theorem steps_mid {s s' : Store H} {f f' : Frame} (vs : List Val) {is is' : List Admin}
    (rest : List Admin) (h : Steps P closedHost ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Steps P closedHost ⟨s, f, vals vs ++ (is ++ rest)⟩ ⟨s', f', vals vs ++ (is' ++ rest)⟩ := by
  simpa [List.append_assoc] using Steps.ctxtInstrs (vs := vs) (rest := rest) h

/-- A trap bubbles out of a sequence. -/
theorem steps_trap (s : Store H) (f : Frame) (vs : List Val) (rest : List Admin) :
    Steps P closedHost ⟨s, f, vals vs ++ (.trap :: rest)⟩ ⟨s, f, [.trap]⟩ := by
  by_cases h : vs ≠ [] ∨ rest ≠ []
  · have := Step.trapInstrs (P := P) (host := closedHost) (s := s) (f := f) h
    simp only [List.append_assoc, List.singleton_append] at this
    exact this.steps
  · simp only [ne_eq, not_or, not_not] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .refl

theorem intBinOp_trap {t : IntType} {op : IntBinOp} {x y : BitVec t.width} {e : IntTrap}
    (h : intBinOp t op x y = .error e) : (instrEffects (.intBinOp t op)).implicitTrap = true := by
  cases op with
  | div sg => rfl
  | rem sg => rfl
  | shr sg => cases sg <;> simp [intBinOp] at h
  | _ => simp [intBinOp] at h

/-- **Evaluation of self-contained trees**, in every store and frame: one constant, or
a trap, and then the tree is flagged `implicitTrap`. -/
theorem sc_eval : ∀ (e : BExpr) {t : IntType}, scType e = some t →
    ∀ (s : Store H) (f : Frame),
      (∃ x : BitVec t.width,
        Steps P closedHost ⟨s, f, expression e.lower⟩ ⟨s, f, [.plain (.intConst t x)]⟩) ∨
      ((effects e).implicitTrap = true ∧
        Steps P closedHost ⟨s, f, expression e.lower⟩ ⟨s, f, [.trap]⟩)
  | .op (.intConst t' b) [], t, h, s, f => by
      simp only [scType, Option.some.injEq] at h
      subst h
      exact .inl ⟨b, by simpa [expression] using .refl⟩
  | .op (.intUnOp t' op) [a], t, h, s, f => by
      simp only [scType] at h
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        simp only [Option.some.injEq] at h
        subst h
        have hlow : expression (BExpr.op (.intUnOp t' op) [a]).lower =
            [] ++ (expression a.lower ++ [.plain (.intUnOp t' op)]) := by
          simp [expression]
        rw [hlow]
        rcases sc_eval a hc.2 s f with ⟨x, hx⟩ | ⟨ht, hx⟩
        · refine .inl ⟨intUnOp t' op x, (steps_mid [] [.plain (.intUnOp t' op)] hx).trans ?_⟩
          exact (by simpa using (Step.numeric (P := P) (host := closedHost) (s := s) (f := f)
            (NumericStep.intUnOp (t := t') (op := op) (x := x))).steps)
        · refine .inr ⟨by simp [effects, effectsList, Effects.merge, ht],
            (steps_mid [] [.plain (.intUnOp t' op)] hx).trans ?_⟩
          simpa using steps_trap (P := P) s f [] [.plain (.intUnOp t' op)]
      · cases h
  | .op (.intBinOp t' op) [a, b], t, h, s, f => by
      simp only [scType] at h
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        simp only [Option.some.injEq] at h
        subst h
        have hlow : expression (BExpr.op (.intBinOp t' op) [a, b]).lower =
            [] ++ (expression a.lower ++ (expression b.lower ++ [.plain (.intBinOp t' op)])) := by
          simp [expression]
        rw [hlow]
        rcases sc_eval a hc.1 s f with ⟨x, hx⟩ | ⟨ht, hx⟩
        · have r₁ := steps_mid [] (expression b.lower ++ [.plain (.intBinOp t' op)]) hx
          rcases sc_eval b hc.2 s f with ⟨y, hy⟩ | ⟨ht, hy⟩
          · have r₂ := steps_mid [Val.num ⟨.int t', x⟩] [.plain (.intBinOp t' op)] hy
            have r₁' : Steps P closedHost
                ⟨s, f, [] ++ (expression a.lower ++
                  (expression b.lower ++ [.plain (.intBinOp t' op)]))⟩
                ⟨s, f, vals [Val.num ⟨.int t', x⟩] ++
                  (expression b.lower ++ [.plain (.intBinOp t' op)])⟩ := by
              simpa [vals, Val.toAdmin] using r₁
            cases hz : intBinOp t' op x y with
            | ok z =>
              refine .inl ⟨z, r₁'.trans (r₂.trans ?_)⟩
              exact (by simpa [vals, Val.toAdmin] using (Step.numeric (P := P) (host := closedHost)
                (s := s) (f := f) (NumericStep.intBinOp hz)).steps)
            | error er =>
              refine .inr ⟨?_, r₁'.trans (r₂.trans ?_)⟩
              · have := intBinOp_trap hz
                simp [effects, effectsList, Effects.merge, this]
              · exact (by simpa [vals, Val.toAdmin] using (Step.numeric (P := P)
                  (host := closedHost) (s := s) (f := f) (NumericStep.intBinOpTrap hz)).steps)
          · refine .inr ⟨by simp [effects, effectsList, Effects.merge, ht], ?_⟩
            have r₂ := steps_mid [Val.num ⟨.int t', x⟩] [.plain (.intBinOp t' op)] hy
            have r₁' : Steps P closedHost
                ⟨s, f, [] ++ (expression a.lower ++
                  (expression b.lower ++ [.plain (.intBinOp t' op)]))⟩
                ⟨s, f, vals [Val.num ⟨.int t', x⟩] ++
                  (expression b.lower ++ [.plain (.intBinOp t' op)])⟩ := by
              simpa [vals, Val.toAdmin] using r₁
            have r₃ := steps_trap (P := P) s f [Val.num ⟨.int t', x⟩] [.plain (.intBinOp t' op)]
            exact r₁'.trans (r₂.trans (by simpa using r₃))
        · refine .inr ⟨by simp [effects, effectsList, Effects.merge, ht], ?_⟩
          have r₁ := steps_mid [] (expression b.lower ++ [.plain (.intBinOp t' op)]) hx
          have r₃ := steps_trap (P := P) s f [] (expression b.lower ++ [.plain (.intBinOp t' op)])
          exact r₁.trans (by simpa using r₃)
      · cases h
  | .op (.intTestOp t' op) [a], t, h, s, f => by
      simp only [scType] at h
      split at h
      · next hc =>
        simp only [beq_iff_eq] at hc
        simp only [Option.some.injEq] at h
        subst h
        have hlow : expression (BExpr.op (.intTestOp t' op) [a]).lower =
            [] ++ (expression a.lower ++ [.plain (.intTestOp t' op)]) := by
          simp [expression]
        rw [hlow]
        rcases sc_eval a hc s f with ⟨x, hx⟩ | ⟨ht, hx⟩
        · refine .inl ⟨intTestOp t' op x, (steps_mid [] [.plain (.intTestOp t' op)] hx).trans ?_⟩
          exact (by simpa [constI32, Val.i32, Val.toAdmin] using (Step.numeric (P := P)
            (host := closedHost) (s := s) (f := f)
            (NumericStep.intTestOp (t := t') (op := op) (x := x))).steps)
        · refine .inr ⟨by simp [effects, effectsList, Effects.merge, ht],
            (steps_mid [] [.plain (.intTestOp t' op)] hx).trans ?_⟩
          simpa using steps_trap (P := P) s f [] [.plain (.intTestOp t' op)]
      · cases h
  | .op (.intRelOp t' op) [a, b], t, h, s, f => by
      simp only [scType] at h
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        simp only [Option.some.injEq] at h
        subst h
        have hlow : expression (BExpr.op (.intRelOp t' op) [a, b]).lower =
            [] ++ (expression a.lower ++ (expression b.lower ++ [.plain (.intRelOp t' op)])) := by
          simp [expression]
        rw [hlow]
        rcases sc_eval a hc.1 s f with ⟨x, hx⟩ | ⟨ht, hx⟩
        · have r₁ := steps_mid [] (expression b.lower ++ [.plain (.intRelOp t' op)]) hx
          have r₁' : Steps P closedHost
              ⟨s, f, [] ++ (expression a.lower ++
                (expression b.lower ++ [.plain (.intRelOp t' op)]))⟩
              ⟨s, f, vals [Val.num ⟨.int t', x⟩] ++
                (expression b.lower ++ [.plain (.intRelOp t' op)])⟩ := by
            simpa [vals, Val.toAdmin] using r₁
          rcases sc_eval b hc.2 s f with ⟨y, hy⟩ | ⟨ht, hy⟩
          · have r₂ := steps_mid [Val.num ⟨.int t', x⟩] [.plain (.intRelOp t' op)] hy
            refine .inl ⟨intRelOp t' op x y, r₁'.trans (r₂.trans ?_)⟩
            exact (by simpa [vals, Val.toAdmin, constI32, Val.i32] using (Step.numeric (P := P)
              (host := closedHost) (s := s) (f := f)
              (NumericStep.intRelOp (t := t') (op := op) (x := x) (y := y))).steps)
          · refine .inr ⟨by simp [effects, effectsList, Effects.merge, ht], ?_⟩
            have r₂ := steps_mid [Val.num ⟨.int t', x⟩] [.plain (.intRelOp t' op)] hy
            have r₃ := steps_trap (P := P) s f [Val.num ⟨.int t', x⟩] [.plain (.intRelOp t' op)]
            exact r₁'.trans (r₂.trans (by simpa using r₃))
        · refine .inr ⟨by simp [effects, effectsList, Effects.merge, ht], ?_⟩
          have r₁ := steps_mid [] (expression b.lower ++ [.plain (.intRelOp t' op)]) hx
          have r₃ := steps_trap (P := P) s f [] (expression b.lower ++ [.plain (.intRelOp t' op)])
          exact r₁.trans (by simpa using r₃)
      · cases h

theorem codeConfig_nil (s : Store H) (f : Frame) (vs : List Val) :
    codeConfig s f vs [] = ⟨s, f, vals vs⟩ := by simp [codeConfig, expression]

/-- The last value of a stack typed below `ts ++ [i32]` is an `i32`. -/
theorem split_last_i32 {s : Store H} {Δ : TypeCtx} {vs : List Val} {ps ts : List CValType}
    (hv : List.Forall₂ (ValOk s) vs ps) (hs : ResultSub Δ ps (ts ++ [.i32])) :
    ∃ vs' c, vs = vs' ++ [Val.i32 c] := by
  have hl₁ := List.Forall₂.length_eq hv
  have hl₂ := resultSub_length hs
  simp only [List.length_append, List.length_singleton] at hl₂
  rcases List.eq_nil_or_concat vs with rfl | ⟨vs', v, rfl⟩
  · have := hl₁
    simp only [List.length_nil] at this
    omega
  rcases List.eq_nil_or_concat ps with rfl | ⟨ps', p, rfl⟩
  · simp at hl₂
  simp only [List.concat_eq_append] at hv hs hl₁ hl₂ ⊢
  have hl₃ : ps'.length = ts.length := by simpa using hl₂
  obtain ⟨-, hp⟩ := resultSub_append_inv hs hl₃
  have hvp : ValOk s v p := by
    have := (forall₂_append_inv hv (by simpa using hl₁)).2
    cases this with
    | cons h _ => exact h
  cases hp with
  | cons hsub _ =>
    cases hvp with
    | num nv =>
      obtain ⟨ty, b⟩ := nv
      simp only [Ty.i32] at hsub
      cases hsub
      exact ⟨vs', b, rfl⟩
    | vec b => cases hsub
    | ref h => cases hsub

end Run

section Local

theorem removable_false_implicitTrap {f : Effects} (h : f.removable false = true) :
    f.implicitTrap = false := by
  cases hf : f.implicitTrap <;> simp_all [Effects.removable]

variable {o : GrowKind → Nat → Nat → Nat → Bool}

theorem joinable_nop (C : Context) (it : InstrType) :
    Joinable (Profile.deterministic o) C it [] [.op .nop []] := by
  intro H s f vs _
  refine ⟨⟨s, f, vals vs⟩, by rw [codeConfig_nil], ?_⟩
  have := steps_mid (P := Profile.deterministic o) vs []
    (Step.parametric (host := closedHost) (s := s) (f := f) ParametricStep.nop).steps
  simpa [codeConfig, expression] using this

theorem joinable_drop_sc {e : BExpr} {t : IntType} (ht : scType e = some t)
    (hi : (effects e).implicitTrap = false) (C : Context) (it : InstrType) :
    Joinable (Profile.deterministic o) C it [] [.op .drop [e]] := by
  intro H s f vs _
  refine ⟨⟨s, f, vals vs⟩, by rw [codeConfig_nil], ?_⟩
  have hc : codeConfig s f vs [.op .drop [e]] =
      ⟨s, f, vals vs ++ (expression e.lower ++ [.plain .drop])⟩ := by
    simp [codeConfig, expression]
  rw [hc]
  rcases sc_eval (P := Profile.deterministic o) e ht s f with ⟨x, hx⟩ | ⟨htr, -⟩
  · have r₁ := steps_mid vs [.plain .drop] hx
    have r₂ := steps_mid (P := Profile.deterministic o) vs []
      (Step.parametric (host := closedHost) (s := s) (f := f)
        (ParametricStep.drop (Val.num ⟨.int t, x⟩))).steps
    exact r₁.trans (by simpa [Val.toAdmin] using r₂)
  · rw [hi] at htr; cases htr

theorem joinable_if_empty {C : Context} {it : InstrType} (hC : C.Wf)
    (hty : SeqOk C [.if_ .empty [] [] []] it) :
    Joinable (Profile.deterministic o) C it [.op .drop []] [.if_ .empty [] [] []] := by
  intro H s f vs hfit
  change InstrsOk C [.if_ .empty [] []] it at hty
  obtain ⟨ts, it₀, -, hi, hs⟩ := single_inv' hC hty
  have hit₀ : it₀ = .plain [.i32] [] := by
    cases hi with
    | if_ hbt _ _ => cases hbt; rfl
    | _ => rename_i h; cases h
  subst hit₀
  obtain ⟨vs', c, rfl⟩ := split_last_i32 hfit.2.2 (by simpa using hs.1)
  refine ⟨⟨s, f, vals vs'⟩, ?_, ?_⟩
  · -- `drop`
    have := steps_mid (P := Profile.deterministic o) vs' []
      (Step.parametric (host := closedHost) (s := s) (f := f)
        (ParametricStep.drop (Val.i32 c))).steps
    simpa [codeConfig, expression, Val.i32, Val.toAdmin, vals] using this
  · -- `if` with empty arms
    have hblock : Steps (Profile.deterministic o) closedHost
        ⟨s, f, [.plain (.block .empty [])]⟩ ⟨s, f, []⟩ := by
      have h₁ := Step.block (P := Profile.deterministic o) (host := closedHost) (s := s) (f := f)
        (bt := .empty) (body := []) (vs := []) (t₁ := []) (t₂ := []) rfl rfl
      have h₂ := Step.labelVals (P := Profile.deterministic o) (host := closedHost) (s := s)
        (f := f) (n := 0) (cont := []) (vs := [])
      simpa [vals, expression] using h₁.steps.trans h₂.steps
    have hif : Steps (Profile.deterministic o) closedHost
        ⟨s, f, [constI32 c, .plain (.if_ .empty [] [])]⟩ ⟨s, f, []⟩ := by
      by_cases hc0 : c = 0
      · subst hc0
        exact (Step.ifFalse (P := Profile.deterministic o) (host := closedHost)).steps.trans hblock
      · exact (Step.ifTrue (P := Profile.deterministic o) (host := closedHost) hc0).steps.trans
          hblock
    have := steps_mid vs' [] hif
    simpa [codeConfig, expression, constI32, Val.i32, Val.toAdmin, vals, BExpr.lower] using this

end Local

/-- **Code heading to a trap traps**: `headsToTrap` code before `unreachable`, from a
fitting configuration, reaches a trap (it is straight-line and leaves by no label). -/
theorem heads_run_trap {P : Profile} {e : BExpr} (he : headsToTrap e = true) {C : Context}
    {it : InstrType} (hC : C.Wf) (hty : SeqOk C [e, .op .unreachable []] it) {H : Type}
    {s : Store H} {f : Frame} {vs : List Val} (hfit : Fits C it s f vs) :
    ∃ (c : Config H) (junk : List Admin), c.code = .trap :: junk ∧
      Steps P closedHost (codeConfig s f vs [e, .op .unreachable []]) c := by
  simp only [headsToTrap, Bool.and_eq_true] at he
  obtain ⟨⟨⟨⟨⟨-, ha⟩, hb⟩, hbt⟩, hc⟩, hm⟩ := he
  have ha' : (effects e).any = false := by simpa using ha
  have hsl := lower_sl e ha' (by simpa using hc) (by simpa using hm) (by simpa using hb)
  have hnolab : ∀ l, l ∉ instrsLabels e.lower := by
    intro l hl
    have := lower_labels e ha' l hl
    simp only [List.isEmpty_iff] at hbt
    rw [hbt] at this
    cases this
  have hty' : InstrsOk C (e.lower ++ [.unreachable]) it := by
    simpa [SeqOk] using hty
  obtain ⟨m, xs₁, xs₂, h₁, -, -⟩ := InstrsOk.split hC hty' rfl
  obtain ⟨s', f', code, hrun, -, hout⟩ := sl_eval' (P := P) e.lower hsl C ⟨it.params, xs₁, m⟩ hC h₁
    s f vs (StOk.of_frameOk hfit.1 hfit.2.1) (hfit.2.2.imp fun _ _ h => .of_valOk h)
  have hc : codeConfig s f vs [e, .op .unreachable []] =
      ⟨s, f, vals vs ++ (expression e.lower ++ [.plain .unreachable])⟩ := by
    simp [codeConfig, expression]
  rw [hc]
  have hlift' : Steps P closedHost ⟨s, f, vals vs ++ (expression e.lower ++ [.plain .unreachable])⟩
      ⟨s', f', code ++ [.plain .unreachable]⟩ := by
    simpa using steps_mid' (P := P) [] [.plain .unreachable] hrun
  rcases hout with ⟨ws, rfl, -, -⟩ | rfl | ⟨l, -, -, -, -, -, hl, -⟩
  · refine ⟨⟨s', f', [.trap]⟩, [], rfl, hlift'.trans ?_⟩
    have h₂ : Steps P closedHost ⟨s', f', vals ws ++ [.plain .unreachable]⟩
        ⟨s', f', vals ws ++ [.trap]⟩ := by
      simpa using steps_mid' (P := P) ws [] (Step.parametric (P := P) (host := closedHost)
        (s := s') (f := f') ParametricStep.unreachable).steps
    exact h₂.trans (by simpa using steps_trap' (P := P) s' f' ws [])
  · exact ⟨⟨s', f', [.trap, .plain .unreachable]⟩, [.plain .unreachable], rfl, hlift'⟩
  · exact absurd hl (hnolab _)

/-! ## trapsNeverHappen rewrites -/

section Tnh

variable {o : GrowKind → Nat → Nat → Nat → Bool}

/-- Running `drop e` for a self-contained `e` that evaluates to a constant. -/
theorem drop_sc_run {P : Profile} {H : Type} {e : BExpr} {t : IntType} {s : Store H} {f : Frame}
    {x : BitVec t.width} (vs : List Val)
    (hx : Steps P closedHost ⟨s, f, expression e.lower⟩ ⟨s, f, [.plain (.intConst t x)]⟩) :
    Steps P closedHost ⟨s, f, vals vs ++ (expression e.lower ++ [.plain .drop])⟩
      ⟨s, f, vals vs⟩ := by
  have r₁ := steps_mid vs [.plain .drop] hx
  have r₂ := steps_mid (P := P) vs []
    (Step.parametric (host := closedHost) (s := s) (f := f)
      (ParametricStep.drop (Val.num ⟨.int t, x⟩))).steps
  exact r₁.trans (by simpa [Val.toAdmin] using r₂)

/-- A stack typed below `ts ++ t₁ ++ [i32]` splits accordingly. -/
theorem split_if_stack {H : Type} {s : Store H} {Δ : TypeCtx} {vs : List Val}
    {ps ts t₁ : List CValType}
    (hv : List.Forall₂ (ValOk s) vs ps) (hs : ResultSub Δ ps (ts ++ (t₁ ++ [.i32]))) :
    ∃ vs₁ args c, vs = vs₁ ++ args ++ [Val.i32 c] ∧ args.length = t₁.length := by
  obtain ⟨vs', c, rfl⟩ := split_last_i32 (Δ := Δ) (ts := ts ++ t₁) hv
    (by simpa [List.append_assoc] using hs)
  have hl₁ := List.Forall₂.length_eq hv
  have hl₂ := resultSub_length hs
  simp only [List.length_append, List.length_singleton] at hl₁ hl₂
  refine ⟨vs'.take ts.length, vs'.drop ts.length, c, by simp, ?_⟩
  simp only [List.length_drop]
  omega

/-- A block whose body is `unreachable` traps. -/
theorem block_unr_trap {P : Profile} {H : Type} {s : Store H} {f : Frame} {bt : BlockType}
    {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁, t₂)) (vs₁ args : List Val)
    (hm : args.length = t₁.length) :
    Steps P closedHost ⟨s, f, vals vs₁ ++ (vals args ++ [.plain (.block bt [.unreachable])])⟩
      ⟨s, f, [.trap]⟩ := by
  have h₁ : Steps P closedHost
      ⟨s, f, vals vs₁ ++ (vals args ++ [.plain (.block bt [.unreachable])])⟩
      ⟨s, f, vals vs₁ ++ [.label t₂.length [] (vals args ++ [.plain .unreachable])]⟩ := by
    simpa [expression] using steps_mid (P := P) vs₁ []
      (Step.block (host := closedHost) (s := s) (f := f) (body := [.unreachable]) hbt hm).steps
  have hin : Steps P closedHost ⟨s, f, vals args ++ [.plain .unreachable]⟩ ⟨s, f, [.trap]⟩ := by
    have h₀ : Steps P closedHost ⟨s, f, vals args ++ [.plain .unreachable]⟩
        ⟨s, f, vals args ++ [.trap]⟩ := by
      simpa using steps_mid (P := P) args []
        (Step.parametric (host := closedHost) (s := s) (f := f) ParametricStep.unreachable).steps
    exact h₀.trans (by simpa using steps_trap (P := P) s f args [])
  have h₂ : Steps P closedHost
      ⟨s, f, vals vs₁ ++ [.label t₂.length [] (vals args ++ [.plain .unreachable])]⟩
      ⟨s, f, vals vs₁ ++ [.trap]⟩ := by
    simpa using steps_mid (P := P) vs₁ [] ((Steps.label (n := t₂.length) (cont := []) hin).trans
      (Step.trapLabel (P := P) (host := closedHost) (s := s) (f := f)).steps)
  exact h₁.trans (h₂.trans (by simpa using steps_trap (P := P) s f vs₁ []))

/-- The `if` rewrites: typing of the `if` gives the stack shape and the block type. -/
theorem if_shape {C : Context} {it : InstrType} (hC : C.Wf) {bt : BlockType}
    {b₁ b₂ : List Instr} (hty : InstrsOk C [.if_ bt b₁ b₂] it)
    {H : Type} {s : Store H} {f : Frame} {vs : List Val} (hfit : Fits C it s f vs) :
    ∃ vs₁ args c t₁ t₂, vs = vs₁ ++ args ++ [Val.i32 c] ∧
      f.module.blockType? bt = some (t₁, t₂) ∧ args.length = t₁.length := by
  obtain ⟨ts, it₀, -, hi, hs⟩ := single_inv' hC hty
  cases hi with
  | @if_ _ _ _ _ t₁ t₂ _ _ hbt _ _ =>
    obtain ⟨vs₁, args, c, rfl, hl⟩ := split_if_stack hfit.2.2 (by simpa using hs.1)
    have htypes : C.types = f.module.types :=
      StateOk.types (C := { C with labels := [], return_ := none }) ⟨hfit.1, hfit.2.1⟩
    obtain ⟨t₁', t₂', hb, hl₁, -⟩ := blockType_of_types htypes hbt
    exact ⟨vs₁, args, c, t₁', t₂', rfl, hb, by omega⟩
  | _ => rename_i h; cases h

end Tnh

/-- TNH vacuum is **not** an equivalence: removing `drop (i32.div_u 1 0)` turns a
trap into a normal return. -/
theorem vacuum_tnh_not_equiv (o : GrowKind → Nat → Nat → Nat → Bool) :
    ¬ SeqRefines (· = ·) (Profile.deterministic o) {} (.plain [] [])
      (vacuum true [.op .drop [divByZero]]) [.op .drop [divByZero]] := by
  intro h
  have hv : vacuum true [.op .drop [divByZero]] = [] := rfl
  rw [hv] at h
  exact TrapCex.not_refines o (h.2.2 (H := Empty) closedHost TrapCex.mod 0 .hole
    closedHost_respectsCode TrapCex.ok_nil TrapCex.ok_trap)

/-! ## Unwrapping a block -/

section Unwrap

/-- The fixed `block_unwrap`: a straight-line body (no loops, no calls) finishes or traps, in
the block and outside it alike. -/
theorem block_unwrap_aux {P : Profile} {C : Context} {it : InstrType} {body : List BExpr}
    (hfree : BExpr.labelsList body = []) (hany : (effectsList body).any = false)
    (hret : (effectsList body).branchesOut = false) (hok : SeqOk C [.block .empty body] it)
    (hloop : (effectsList body).mayNotReturn = false) (hcall : (effectsList body).calls = false)
    (hC : C.Wf) : Joinable P C it [.block .empty body] body := by
  intro H s f vs hfit
  have hty : InstrsOk C [.block .empty (BExpr.lowerList body)] it := by
    simpa [SeqOk, BExpr.lower] using hok
  obtain ⟨ts, it₀, -, hi, -⟩ := single_inv' hC hty
  cases hi with
  | @block _ _ _ t₁ t₂ xs hbt hb =>
    cases hbt
    have hsl := lowerList_sl body hany hcall hloop hret
    obtain ⟨s', f', code, hrun, -, hout⟩ := sl_eval' (P := P) _ hsl (C.withLabel [])
      ⟨[], xs, []⟩ (wf_withLabel hC (by simp [ResultOk])) hb s f []
      ((StOk.of_frameOk hfit.1 hfit.2.1).withLabel []) .nil
    have hA₁ : Steps P closedHost (codeConfig s f vs [.block .empty body])
        ⟨s, f, vals vs ++ [.label 0 [] (expression (BExpr.lowerList body))]⟩ := by
      have := steps_mid' (P := P) vs [] (Step.block (P := P) (host := closedHost) (s := s) (f := f)
        (bt := .empty) (body := BExpr.lowerList body) (vs := []) (t₁ := []) (t₂ := []) rfl
        rfl).steps
      simpa [codeConfig, expression, BExpr.lower] using this
    have hA₂ : Steps P closedHost
        ⟨s, f, vals vs ++ [.label 0 [] (expression (BExpr.lowerList body))]⟩
        ⟨s', f', vals vs ++ [.label 0 [] code]⟩ := by
      simpa using steps_mid' (P := P) vs [] (Steps.label (n := 0) (cont := [])
        (by simpa using hrun))
    have hB : Steps P closedHost (codeConfig s f vs body) ⟨s', f', vals vs ++ code⟩ := by
      simpa [codeConfig] using steps_mid' (P := P) vs [] (by simpa using hrun)
    rcases hout with ⟨ws, rfl, hws, -⟩ | rfl | ⟨l, -, -, -, -, -, hl, -⟩
    · rw [forall₂_nil_inv hws] at hA₂ hB
      refine ⟨⟨s', f', vals vs⟩, hA₁.trans (hA₂.trans ?_), by simpa using hB⟩
      simpa using steps_mid' (P := P) vs [] (Step.labelVals (P := P) (host := closedHost)
        (s := s') (f := f') (n := 0) (cont := []) (vs := [])).steps
    · refine ⟨⟨s', f', [.trap]⟩, hA₁.trans (hA₂.trans ?_), hB.trans ?_⟩
      · have h₁ : Steps P closedHost ⟨s', f', vals vs ++ [.label 0 [] [.trap]]⟩
            ⟨s', f', vals vs ++ [.trap]⟩ := by
          simpa using steps_mid' (P := P) vs [] (Step.trapLabel (P := P) (host := closedHost)
            (s := s') (f := f') (n := 0) (cont := [])).steps
        exact h₁.trans (by simpa using steps_trap' (P := P) s' f' vs [])
      · simpa using steps_trap' (P := P) s' f' vs []
    · have : instrsLabels (BExpr.lowerList body) = [] := hfree
      rw [this] at hl
      cases hl
  | _ => rename_i h; cases h

end Unwrap

/-- **`block_unwrap` as first stated is false**: `block (loop (br 0))` satisfies its
hypotheses (no free label, nothing outside the analysed fragment, no `return`, typed), but
the loop diverges, so the block and its body never reach a common configuration
(`LoopCex.not_joinable`). Hence the flagged extra hypotheses (no loops, no calls). -/
theorem block_unwrap_false_v0 :
    ¬ ∀ (P : Profile) (C : Context) (it : InstrType) (body : List BExpr),
      BExpr.labelsList body = [] → (effectsList body).any = false →
      (effectsList body).branchesOut = false → SeqOk C [.block .empty body] it →
      Joinable P C it [.block .empty body] body := by
  intro h
  exact LoopCex.not_joinable (P := Profile.deterministic fun _ _ _ _ => false)
    (h _ _ _ _ LoopCex.body_labels LoopCex.body_any LoopCex.body_branchesOut LoopCex.body_typed)

/-- **Unwrapping a block nothing branches to** (`RemoveUnusedNames` followed by
`MergeBlocks`, on layer D): with the empty block type, no free branch in the
body, no `return`, no loop, no call and nothing outside the profile, the block and its
body join (the label is popped when the body finishes, or the trap propagates through
it). -/
-- FLAG(statement-change): hypotheses `hloop` (no loop: `mayNotReturn = false`), `hcall`
-- (no call) and `hC : C.Wf` added. Without the first two the statement is false
-- (`block_unwrap_false_v0`: a diverging body never joins); `C.Wf` is needed to invert the
-- body's typing.
theorem block_unwrap {P : Profile} {C : Context} {it : InstrType} {body : List BExpr}
    (hfree : BExpr.labelsList body = []) (hany : (effectsList body).any = false)
    (hret : (effectsList body).branchesOut = false) (hok : SeqOk C [.block .empty body] it)
    (hloop : (effectsList body).mayNotReturn = false) (hcall : (effectsList body).calls = false)
    (hC : C.Wf) :
    Joinable P C it [.block .empty body] body :=
  block_unwrap_aux hfree hany hret hok hloop hcall hC

end Silmaril.Wasm.Binaryen
