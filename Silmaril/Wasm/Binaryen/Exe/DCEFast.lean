module

public import Silmaril.Wasm.Binaryen.Exe.DCEExe

@[expose] public section

/-! # Linear-time executable DCE

`Exe/DCEExe.lean` follows the specification literally: every node of `dceE`/`dceL`
asks `BExpr.listBot` of its result, which walks the whole subtree and lowers every
block body it meets to read its free labels (`BExpr.labelsList`), and the safety
check `dceSafeWB` recomputes `dceL` of every operand list and lowers it again to read
its last instruction. On deeply nested bodies (an interpreter's `br_table` dispatch)
that is quadratic or worse in the nesting depth.

`dceL3` computes the three results in one bottom-up pass: the DCE output, whether it
is bottom, and the safety check. Free labels are tested without lowering
(`hasLabelL`), and the last lowered instruction is read off the last tree
(`endsBotL`). `dceL3_eq` proves it equal to the specification, and `dceChecked` is
replaced by `dceCheckedFast` in compiled code (`@[csimp]`), so outputs are unchanged
and every theorem about `Dce.dceChecked` still applies.
-/

namespace Silmaril.Wasm.Binaryen.Exe.Dce

open Silmaril.Wasm Silmaril.Wasm.Binaryen

mutual
/-- Is `d` a free branch target of the lowering of a tree? -/
def hasLabelE (d : Nat) : BExpr → Bool
  | .op i args => hasLabelL d args || (instrLabels i).contains d
  | .block _ b => hasLabelL (d + 1) b
  | .loop _ b => hasLabelL (d + 1) b
  | .if_ _ c t e => hasLabelL d c || (hasLabelL (d + 1) t || hasLabelL (d + 1) e)
  | .tryTable _ cs b => (cs.map Catch.label).contains d || hasLabelL (d + 1) b
/-- Is `d` a free branch target of the lowering of a sequence? -/
def hasLabelL (d : Nat) : List BExpr → Bool
  | [] => false
  | e :: es => hasLabelE d e || hasLabelL d es
end

/-- Does the lowering of a sequence end in a bottom instruction? Every tree lowers to a
nonempty sequence that ends in the operator of an `op` node, or in one structured
instruction, which is never bottom. -/
def endsBotL (es : List BExpr) : Bool :=
  match es.getLast? with
  | some (.op i _) => botInstr i
  | _ => false

mutual
/-- `(dceE e, BExpr.listBot (dceE e), dceSafeWEB e)` in one pass. -/
def dceE3 : BExpr → List BExpr × Bool × Bool
  | .op i args =>
      let (a, ab, s) := dceL3 args
      if ab then (a, true, s && endsBotL a) else ([.op i a], botInstr i, s)
  | .block bt b =>
      let (b', bb, s) := dceL3 b
      ([.block bt b'], bb && !hasLabelL 0 b', s)
  | .loop bt b =>
      let (b', bb, s) := dceL3 b
      ([.loop bt b'], bb, s)
  | .if_ bt c t e =>
      let (c', cb, cs) := dceL3 c
      if cb then (c', true, cs && endsBotL c') else
        let (t', tb, ts) := dceL3 t
        let (e', eb, es) := dceL3 e
        ([.if_ bt c' t' e'], tb && eb && !hasLabelL 0 t' && !hasLabelL 0 e', cs && (ts && es))
  | .tryTable bt cs b =>
      let (b', _, s) := dceL3 b
      ([.tryTable bt cs b'], false, s)
/-- `(dceL es, BExpr.listBot (dceL es), dceSafeWB es)` in one pass. -/
def dceL3 : List BExpr → List BExpr × Bool × Bool
  | [] => ([], false, true)
  | e :: es =>
      let (e', eb, s) := dceE3 e
      if eb then (e', true, s && (es.isEmpty || endsBotL e'))
      else
        let (r, rb, rs) := dceL3 es
        (e' ++ r, rb, s && rs)
end

/-- `dceBodyChecked` through `dceL3`. -/
def dceBodyCheckedFast (b : List BExpr) : List BExpr :=
  let (r, _, s) := dceL3 b
  if s then r else b

/-- `dceChecked` through `dceL3`. -/
def dceCheckedFast (m : BModule) : BModule :=
  { m with funcs := m.funcs.map fun f => { f with body := dceBodyCheckedFast f.body } }

/-! ## Equality with the specification -/

private theorem flatMap_attach_val' {α β : Type} (l : List α) (f : α → List β) :
    (l.attach.flatMap fun i => f i.val) = l.flatMap f := by
  conv_rhs => rw [← List.attach_map_subtype_val l]
  rw [List.flatMap_map]

private theorem mem_unbind' {ns : List Nat} {n : Nat} : n ∈ unbind ns ↔ n + 1 ∈ ns := by
  simp only [unbind, List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, h⟩
    split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      have e : a = n + 1 := by omega
      subst e
      exact ha
  · intro h
    exact ⟨n + 1, h, by simp⟩

private theorem instrsLabels_append (a b : List Instr) :
    instrsLabels (a ++ b) = instrsLabels a ++ instrsLabels b := by
  simp [instrsLabels]

private theorem instrsLabels_single (i : Instr) : instrsLabels [i] = instrLabels i := by
  simp [instrsLabels]

private theorem instrLabels_block' (bt : BlockType) (body : List Instr) :
    instrLabels (.block bt body) = unbind (instrsLabels body) := by
  rw [instrLabels.eq_def]
  simp only [flatMap_attach_val', instrsLabels]

private theorem instrLabels_loop' (bt : BlockType) (body : List Instr) :
    instrLabels (.loop bt body) = unbind (instrsLabels body) := by
  rw [instrLabels.eq_def]
  simp only [flatMap_attach_val', instrsLabels]

private theorem instrLabels_if' (bt : BlockType) (t e : List Instr) :
    instrLabels (.if_ bt t e) = unbind (instrsLabels t ++ instrsLabels e) := by
  rw [instrLabels.eq_def]
  simp only [flatMap_attach_val', instrsLabels]

private theorem instrLabels_tryTable' (bt : BlockType) (cs : List Catch) (body : List Instr) :
    instrLabels (.tryTable bt cs body) = cs.map Catch.label ++ unbind (instrsLabels body) := by
  rw [instrLabels.eq_def]
  simp only [flatMap_attach_val', instrsLabels]

mutual
theorem hasLabelE_iff (d : Nat) : ∀ e : BExpr,
    hasLabelE d e = true ↔ d ∈ instrsLabels e.lower
  | .op i args => by
      simp only [hasLabelE, BExpr.lower, instrsLabels_append, instrsLabels_single,
        Bool.or_eq_true, List.contains_iff_mem, List.mem_append, hasLabelL_iff d args]
  | .block bt b => by
      simp only [hasLabelE, BExpr.lower, instrsLabels_single, instrLabels_block', mem_unbind',
        hasLabelL_iff (d + 1) b]
  | .loop bt b => by
      simp only [hasLabelE, BExpr.lower, instrsLabels_single, instrLabels_loop', mem_unbind',
        hasLabelL_iff (d + 1) b]
  | .if_ bt c t e => by
      simp only [hasLabelE, BExpr.lower, instrsLabels_append, instrsLabels_single,
        instrLabels_if', mem_unbind', Bool.or_eq_true, List.mem_append, hasLabelL_iff d c,
        hasLabelL_iff (d + 1) t, hasLabelL_iff (d + 1) e]
  | .tryTable bt cs b => by
      simp only [hasLabelE, BExpr.lower, instrsLabels_single, instrLabels_tryTable',
        mem_unbind', Bool.or_eq_true, List.contains_iff_mem, List.mem_append,
        hasLabelL_iff (d + 1) b]
theorem hasLabelL_iff (d : Nat) : ∀ es : List BExpr,
    hasLabelL d es = true ↔ d ∈ instrsLabels (BExpr.lowerList es)
  | [] => by simp [hasLabelL, instrsLabels]
  | e :: es => by
      simp only [hasLabelL, BExpr.lowerList, instrsLabels_append, Bool.or_eq_true,
        List.mem_append, hasLabelE_iff d e, hasLabelL_iff d es]
end

theorem hasLabelL_eq (d : Nat) (es : List BExpr) :
    hasLabelL d es = (BExpr.labelsList es).contains d := by
  rw [Bool.eq_iff_iff, hasLabelL_iff, BExpr.labelsList, List.contains_iff_mem]

private theorem lower_ne_nil : ∀ e : BExpr, e.lower ≠ []
  | .op _ _ | .block _ _ | .loop _ _ | .if_ _ _ _ _ | .tryTable _ _ _ => by simp [BExpr.lower]

private theorem endsInBotB_lower (e : BExpr) :
    endsInBotB e.lower = endsBotL [e] := by
  cases e <;> simp [endsInBotB, endsBotL, BExpr.lower, botInstr]

theorem endsBotL_eq : ∀ es : List BExpr, endsInBotB (BExpr.lowerList es) = endsBotL es
  | [] => rfl
  | [e] => by simp [endsInBotB_lower]
  | e :: e' :: es => by
      have ih := endsBotL_eq (e' :: es)
      have hne : BExpr.lowerList (e' :: es) ≠ [] := by
        simp [BExpr.lowerList, lower_ne_nil]
      rw [BExpr.lowerList_cons, endsInBotB, List.getLast?_append_of_ne_nil _ hne, ← endsInBotB,
        ih]
      simp [endsBotL]

theorem listBot_append (a b : List BExpr) :
    BExpr.listBot (a ++ b) = (BExpr.listBot a || BExpr.listBot b) := by
  induction a with
  | nil => simp [BExpr.listBot]
  | cons e es ih => simp [BExpr.listBot, ih, Bool.or_assoc]

private theorem listBot_single (e : BExpr) : BExpr.listBot [e] = BExpr.isBot e := by
  simp [BExpr.listBot]

mutual
theorem dceE3_eq : ∀ e : BExpr, dceE3 e = (dceE e, BExpr.listBot (dceE e), dceSafeWEB e)
  | .op i args => by
      rw [dceE3, dceL3_eq args]
      by_cases hb : BExpr.listBot (dceL args) = true
      · simp [dceE, dceSafeWEB, hb, endsBotL_eq]
      · simp [dceE, dceSafeWEB, hb, listBot_single, BExpr.isBot]
  | .block bt b => by
      rw [dceE3, dceL3_eq b]
      simp [dceE, dceSafeWEB, listBot_single, BExpr.isBot, hasLabelL_eq]
  | .loop bt b => by
      rw [dceE3, dceL3_eq b]
      simp [dceE, dceSafeWEB, listBot_single, BExpr.isBot]
  | .if_ bt c t e => by
      rw [dceE3, dceL3_eq c, dceL3_eq t, dceL3_eq e]
      by_cases hb : BExpr.listBot (dceL c) = true
      · simp [dceE, dceSafeWEB, hb, endsBotL_eq]
      · simp [dceE, dceSafeWEB, hb, listBot_single, BExpr.isBot, hasLabelL_eq, Bool.and_assoc]
  | .tryTable bt cs b => by
      rw [dceE3, dceL3_eq b]
      simp [dceE, dceSafeWEB, listBot_single, BExpr.isBot]
theorem dceL3_eq : ∀ es : List BExpr, dceL3 es = (dceL es, BExpr.listBot (dceL es), dceSafeWB es)
  | [] => by simp [dceL3, dceL, dceSafeWB, BExpr.listBot]
  | e :: es => by
      rw [dceL3, dceE3_eq e]
      by_cases hb : BExpr.listBot (dceE e) = true
      · simp [dceL, dceSafeWB, hb, endsBotL_eq]
      · rw [dceL3_eq es]
        simp [dceL, dceSafeWB, hb, listBot_append]
end

theorem dceBodyCheckedFast_eq : dceBodyCheckedFast = dceBodyChecked := by
  funext b
  simp only [dceBodyCheckedFast, dceBodyChecked, dceL3_eq]

/-- Compiled code runs the one-pass DCE. -/
@[csimp] theorem dceChecked_eq_fast : @dceChecked = @dceCheckedFast := by
  funext m
  simp only [dceChecked, dceCheckedFast, dceBodyCheckedFast_eq]

end Silmaril.Wasm.Binaryen.Exe.Dce
