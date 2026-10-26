module

public import Silmaril.Courses.Cambridge.OptimisingCompilers.Decompilation
import Std.Data.String.ToNat

/-! # Exercise sheet 4, question 19 (a farboo decompiler)

Source: `cam-optcomp-2025-exercise-sheet-4` in `references.bib`, question 19.


Answer: `decompile`, for the code produced by `Decompilation.Stmt.compile`
(the sheet's patterns, with absolute labels). It pattern-matches the compiled
shapes, as the sheet's hints suggest:

* `MOV %j, v; ALU %(j−1), v′, %j; …; ALU %0, …` is an expression into `%0`;
* an expression followed by `MOV x, %0` is `x = e`;
* an expression followed by `CMPEQ %0, #0 → l` is an `if`: if the instruction
  before `l` is a `NOP` jumping forward past `l`, it is the jump over an `else`
  branch, otherwise there is no `else`;
* `MOV x, #lo; CMPGT x, #hi → l` with `x` not a temporary is a `for` loop
  whose body ends two instructions before `l`;
* a region of code is a statement followed by the rest of the region.

`decompile_compile`: decompiling compiled code gives back the program.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers.Exercises.S4Q19

open Decompilation

/-- Recover a value from an operand. -/
def ofOperand : Operand String → Val
  | .imm n => .num n
  | .var x => .var x

/-- Recover an operator. -/
def ofAlu : AluOp → Option Op
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul
  | _ => none

variable (code : List (Instr String ℕ))

/-- The `ALU` chain of an expression whose current temporary is `cur`, ending at
`%k`. -/
def exprTail (k : ℕ) : ℕ → FExpr → String → ℕ → Option (FExpr × ℕ)
  | 0, _, _, _ => none
  | fuel + 1, e, cur, pc =>
    if cur = temp k then some (e, pc) else
    match code[pc]? with
    | some (.alu op d a (.var c) _) =>
      if c = cur then
        match ofAlu op with
        | some o => exprTail k fuel (.op (ofOperand a) o e) d (pc + 1)
        | none => none
      else none
    | _ => none

/-- An expression computed into `%k` starting at `pc`, and the label after it. -/
def parseExpr (k pc : ℕ) : Option (FExpr × ℕ) :=
  match code[pc]? with
  | some (.alu2 .mov d a _) => exprTail code k (code.length + 1) (.val (ofOperand a)) d (pc + 1)
  | _ => none

mutual

/-- The statements of the region `[pc, stop)`. -/
def decRegion : ℕ → ℕ → ℕ → Option Stmt
  | 0, _, _ => none
  | fuel + 1, pc, stop =>
    match decOne fuel pc with
    | some (s, next) =>
      if next = stop then some s
      else if next < stop then (decRegion fuel next stop).map fun r => .seq s r
      else none
    | none => none

/-- One statement starting at `pc`, and the label after it. -/
def decOne : ℕ → ℕ → Option (Stmt × ℕ)
  | 0, _ => none
  | fuel + 1, pc =>
    match code[pc]?, code[pc + 1]? with
    | some (.alu2 .mov x (.imm lo) _), some (.cmp .gt (.var x') (.imm hi) stop _) =>
      if x = x' ∧ x.startsWith "%" = false then
        (decRegion fuel (pc + 2) (stop - 2)).map fun body => (.forLoop x lo hi body, stop)
      else none
    | _, _ =>
      match parseExpr code 0 pc with
      | some (e, pc') =>
        match code[pc']? with
        | some (.alu2 .mov x (.var t) _) =>
          if t = temp 0 then some (.assign x e, pc' + 1) else none
        | some (.cmp .eq (.var t) (.imm 0) tgt _) =>
          if t = temp 0 then
            match code[tgt - 1]? with
            | some (.nop fin) =>
              if tgt < fin then
                match decRegion fuel (pc' + 1) (tgt - 1), decRegion fuel tgt fin with
                | some st, some se => some (.ifElse e st se, fin)
                | _, _ => none
              else (decRegion fuel (pc' + 1) tgt).map fun body => (.ifThen e body, tgt)
            | _ => (decRegion fuel (pc' + 1) tgt).map fun body => (.ifThen e body, tgt)
          else none
        | _ => none
      | none => none

end

/-- The decompiler. -/
def decompile : Option Stmt := decRegion code (2 * code.length + 2) 0 code.length

/-! ## Correctness of the decompiler

The proof separates the structure of compiled code from the fuel: `At code pc xs`
says that `code` contains `xs` at label `pc`, and `dec_compile` shows, by
structural induction on the statement, that every fuel above twice the length
of the compiled code suffices. -/

/-- `code` contains `xs` starting at label `pc`. -/
def At (code : List (Instr String ℕ)) (pc : ℕ) (xs : List (Instr String ℕ)) : Prop :=
  ∃ pre post, code = pre ++ xs ++ post ∧ pre.length = pc

section At

variable {code : List (Instr String ℕ)} {pc q : ℕ} {xs ys : List (Instr String ℕ)}

theorem At.left (h : At code pc (xs ++ ys)) : At code pc xs := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  exact ⟨pre, ys ++ post, by simp, rfl⟩

theorem At.right (h : At code pc (xs ++ ys)) : At code (pc + xs.length) ys := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  exact ⟨pre ++ xs, post, by simp, by simp⟩

theorem At.right' (h : At code pc (xs ++ ys)) (hq : pc + xs.length = q) : At code q ys :=
  hq ▸ h.right

theorem At.cons {x : Instr String ℕ} (h : At code pc (x :: xs)) :
    code[pc]? = some x ∧ At code (pc + 1) xs := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  refine ⟨?_, pre ++ [x], post, by simp, by simp⟩
  rw [List.append_assoc, List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

theorem At.single {x : Instr String ℕ} (h : At code pc [x]) : code[pc]? = some x :=
  h.cons.1

theorem At.length_le (h : At code pc xs) : pc + xs.length ≤ code.length := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  simp only [List.length_append]
  omega

end At

theorem temp_inj {a b : ℕ} (h : temp a = temp b) : a = b := by
  simpa [temp, Nat.repr_inj] using h

theorem ofOperand_toOperand (v : Val) : ofOperand v.toOperand = v := by
  cases v <;> rfl

theorem ofAlu_toAlu (o : Op) (h : o ≠ .div) : ofAlu ((o.toAlu).getD .add) = some o := by
  cases o <;> simp_all [Op.toAlu, ofAlu]

/-- The innermost value of an expression. -/
def leafOf : FExpr → Val
  | .val v => v
  | .op _ _ e => leafOf e

/-- The number of operators of an expression. -/
def depthOf : FExpr → ℕ
  | .val _ => 0
  | .op _ _ e => depthOf e + 1

theorem length_compile (e : FExpr) (k pc : ℕ) : (e.compile k pc).length = depthOf e + 1 := by
  induction e generalizing k with
  | val v => rfl
  | op v o e ih => simp [FExpr.compile, depthOf, ih]

theorem compile_head (e : FExpr) (k pc : ℕ) : ∃ rest, e.compile k pc =
    .alu2 .mov (temp (k + depthOf e)) (leafOf e).toOperand (pc + 1) :: rest := by
  induction e generalizing k with
  | val v => exact ⟨[], rfl⟩
  | op v o e ih =>
    obtain ⟨rest, hr⟩ := ih (k + 1)
    have hk : k + depthOf (.op v o e) = k + 1 + depthOf e := by simp only [depthOf]; omega
    refine ⟨rest ++ [.alu ((o.toAlu).getD .add) (temp k) v.toOperand (.var (temp (k + 1)))
      (pc + (e.compile (k + 1) pc).length + 1)], ?_⟩
    rw [hk]
    simp only [FExpr.compile, leafOf]
    rw [hr]
    rfl

theorem compile_no_cmp (e : FExpr) (k pc : ℕ) :
    ∀ y ∈ e.compile k pc, ∀ c a b t n, y ≠ .cmp c a b t n := by
  induction e generalizing k with
  | val v =>
    intro y hy c a b t n h
    simp only [FExpr.compile, List.mem_singleton] at hy
    subst hy
    cases h
  | op v o e ih =>
    intro y hy c a b t n h
    simp only [FExpr.compile, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact ih (k + 1) y hy c a b t n h
    · cases h

variable {code} in
/-- Inside compiled code the `ALU` chain is consumed one operator per unit of
fuel, rebuilding the expression from its innermost value outwards. -/
theorem exprTail_compile (e : FExpr) (he : e.Supported) (k pc kk fuel : ℕ) (hkk : kk ≤ k)
    (h : At code pc (e.compile k pc)) :
    exprTail code kk (fuel + depthOf e) (.val (leafOf e)) (temp (k + depthOf e)) (pc + 1) =
      exprTail code kk fuel e (temp k) (pc + (e.compile k pc).length) := by
  induction e generalizing k fuel with
  | val v => simp [depthOf, leafOf, FExpr.compile]
  | op v o e ih =>
    obtain ⟨-, ho, he⟩ := he
    have h' : At code pc (e.compile (k + 1) pc ++
        [.alu ((o.toAlu).getD .add) (temp k) v.toOperand (.var (temp (k + 1)))
          (pc + (e.compile (k + 1) pc).length + 1)]) := h
    have hne : temp (k + 1) ≠ temp kk := fun h => by have := temp_inj h; omega
    have hc := (h'.right' rfl).single
    rw [show fuel + depthOf (.op v o e) = fuel + 1 + depthOf e by simp only [depthOf]; omega,
      show k + depthOf (.op v o e) = k + 1 + depthOf e by simp only [depthOf]; omega]
    simp only [leafOf]
    rw [ih he (k + 1) (fuel + 1) (by omega) h'.left]
    simp [exprTail, hne, hc, ofAlu_toAlu o ho, ofOperand_toOperand, FExpr.compile, Nat.add_assoc]

variable {code} in
theorem parseExpr_compile (e : FExpr) (he : e.Supported) (pc : ℕ)
    (h : At code pc (e.compile 0 pc)) :
    parseExpr code 0 pc = some (e, pc + (e.compile 0 pc).length) := by
  obtain ⟨rest, hr⟩ := compile_head e 0 pc
  have h0 : code[pc]? =
      some (.alu2 .mov (temp (0 + depthOf e)) (leafOf e).toOperand (pc + 1)) := by
    have h' := h
    rw [hr] at h'
    exact h'.cons.1
  have hlen := h.length_le
  rw [length_compile] at hlen
  have key := exprTail_compile e he 0 pc 0 (code.length + 1 - depthOf e) (le_refl 0) h
  rw [show code.length + 1 - depthOf e + depthOf e = code.length + 1 by omega] at key
  obtain ⟨g, hg⟩ : ∃ g, code.length + 1 - depthOf e = g + 1 := ⟨code.length - depthOf e, by omega⟩
  rw [hg] at key
  unfold parseExpr
  rw [h0]
  simp only [ofOperand_toOperand]
  rw [key]
  simp [exprTail]

/-- The last instruction of a compiled statement is not a forward `NOP` past the
statement's end. -/
theorem compile_last (s : Stmt) (pc : ℕ) : ∃ L i, s.compile pc = L ++ [i] ∧
    ∀ fin, i = .nop fin → fin < pc + L.length + 1 := by
  induction s generalizing pc with
  | assign x e => exact ⟨e.compile 0 pc, _, rfl, fun _ h => by cases h⟩
  | forLoop x lo hi b _ =>
    refine ⟨[.alu2 .mov x (.imm lo) (pc + 1), .cmp .gt (.var x) (.imm hi)
        (pc + 2 + (b.compile (pc + 2)).length + 2) (pc + 2)] ++ b.compile (pc + 2) ++
        [.alu .add x (.var x) (.imm 1) (pc + 2 + (b.compile (pc + 2)).length + 1)], .nop (pc + 1),
        by simp [Stmt.compile], ?_⟩
    intro fin h
    cases h
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  | ifThen c b ih =>
    obtain ⟨L, i, hL, hi⟩ := ih (pc + (c.compile 0 pc).length + 1)
    refine ⟨c.compile 0 pc ++ [.cmp .eq (.var (temp 0)) (.imm 0)
        (pc + (c.compile 0 pc).length + 1 + (L ++ [i]).length)
        (pc + (c.compile 0 pc).length + 1)] ++ L, i, ?_, fun fin h => ?_⟩
    · simp [Stmt.compile, hL]
    · have := hi fin h
      simp only [List.length_append, List.length_singleton]
      omega
  | ifElse c t e _ ih =>
    obtain ⟨L, i, hL, hi⟩ := ih (pc + (c.compile 0 pc).length + 1 +
      (t.compile (pc + (c.compile 0 pc).length + 1)).length + 1)
    refine ⟨c.compile 0 pc ++ [.cmp .eq (.var (temp 0)) (.imm 0)
        (pc + (c.compile 0 pc).length + 1 +
          (t.compile (pc + (c.compile 0 pc).length + 1)).length + 1)
        (pc + (c.compile 0 pc).length + 1)] ++ t.compile (pc + (c.compile 0 pc).length + 1) ++
        [.nop (pc + (c.compile 0 pc).length + 1 +
          (t.compile (pc + (c.compile 0 pc).length + 1)).length + 1 + (L ++ [i]).length)] ++ L,
        i, ?_, fun fin h => ?_⟩
    · simp [Stmt.compile, hL]
    · have := hi fin h
      simp only [List.length_append, List.length_singleton]
      omega
  | seq s₁ s₂ _ ih =>
    obtain ⟨L, i, hL, hi⟩ := ih (pc + (s₁.compile pc).length)
    refine ⟨s₁.compile pc ++ L, i, ?_, fun fin h => ?_⟩
    · simp [Stmt.compile, hL]
    · have := hi fin h
      simp only [List.length_append]
      omega

theorem compile_length_pos (s : Stmt) (pc : ℕ) : 0 < (s.compile pc).length := by
  obtain ⟨L, i, hL, -⟩ := compile_last s pc
  simp [hL]

/-- The non-loop branch of `decOne`: statements that start with an expression. -/
def decRest (fuel pc : ℕ) : Option (Stmt × ℕ) :=
  match parseExpr code 0 pc with
  | some (e, pc') =>
    match code[pc']? with
    | some (.alu2 .mov x (.var t) _) =>
      if t = temp 0 then some (.assign x e, pc' + 1) else none
    | some (.cmp .eq (.var t) (.imm 0) tgt _) =>
      if t = temp 0 then
        match code[tgt - 1]? with
        | some (.nop fin) =>
          if tgt < fin then
            match decRegion code fuel (pc' + 1) (tgt - 1), decRegion code fuel tgt fin with
            | some st, some se => some (.ifElse e st se, fin)
            | _, _ => none
          else (decRegion code fuel (pc' + 1) tgt).map fun body => (.ifThen e body, tgt)
        | _ => (decRegion code fuel (pc' + 1) tgt).map fun body => (.ifThen e body, tgt)
      else none
    | _ => none
  | none => none

theorem decOne_succ_of_not_for {f pc : ℕ}
    (h : ∀ x lo x' hi stop n₁ n₂, code[pc]? = some (.alu2 .mov x (.imm lo) n₁) →
      code[pc + 1]? ≠ some (.cmp .gt (.var x') (.imm hi) stop n₂)) :
    decOne code (f + 1) pc = decRest code f pc := by
  simp only [decOne]
  split
  · rename_i h₁ h₂
    exact absurd h₂ (h _ _ _ _ _ _ _ h₁)
  · rfl

variable {code} in
theorem not_for_of_expr {e : FExpr} {k pc : ℕ} {y : Instr String ℕ}
    (h : At code pc (e.compile k pc ++ [y])) (hy : ∀ a b t n, y ≠ .cmp .gt a b t n) :
    ∀ x lo x' hi stop n₁ n₂, code[pc]? = some (.alu2 .mov x (.imm lo) n₁) →
      code[pc + 1]? ≠ some (.cmp .gt (.var x') (.imm hi) stop n₂) := by
  intro x lo x' hi stop n₁ n₂ _ h₁
  obtain ⟨pre, post, rfl, rfl⟩ := h
  have hlen : 1 < (e.compile k pre.length ++ [y]).length := by
    simp [length_compile]
  rw [List.append_assoc, List.getElem?_append_right (by omega),
    show pre.length + 1 - pre.length = 1 by omega, List.getElem?_append_left hlen,
    List.getElem?_eq_getElem hlen, Option.some.injEq] at h₁
  have hm := List.getElem_mem hlen
  rw [h₁] at hm
  simp only [List.mem_append, List.mem_singleton] at hm
  rcases hm with hm | hm
  · exact compile_no_cmp e k pre.length _ hm _ _ _ _ _ rfl
  · exact hy _ _ _ _ hm.symm

theorem decOne_for {f pc stop n₁ n₂ : ℕ} {x : String} {lo hi : ℤ} {b : Stmt}
    (h₀ : code[pc]? = some (.alu2 .mov x (.imm lo) n₁))
    (h₁ : code[pc + 1]? = some (.cmp .gt (.var x) (.imm hi) stop n₂))
    (hx : x.startsWith "%" = false)
    (hb : decRegion code f (pc + 2) (stop - 2) = some b) :
    decOne code (f + 1) pc = some (.forLoop x lo hi b, stop) := by
  simp [decOne, h₀, h₁, hx, hb]

theorem decRest_assign {f pc p' n : ℕ} {e : FExpr} {x : String}
    (hp : parseExpr code 0 pc = some (e, p'))
    (hc : code[p']? = some (.alu2 .mov x (.var (temp 0)) n)) :
    decRest code f pc = some (.assign x e, p' + 1) := by
  simp [decRest, hp, hc]

theorem decRest_ifThen {f pc p' tgt n : ℕ} {e : FExpr} {b : Stmt}
    (hp : parseExpr code 0 pc = some (e, p'))
    (hc : code[p']? = some (.cmp .eq (.var (temp 0)) (.imm 0) tgt n))
    (hl : ∀ fin, code[tgt - 1]? = some (.nop fin) → fin ≤ tgt)
    (hb : decRegion code f (p' + 1) tgt = some b) :
    decRest code f pc = some (.ifThen e b, tgt) := by
  simp only [decRest, hp, hc, ↓reduceIte]
  split
  · rename_i fin hfin
    have hnl : ¬ tgt < fin := by have := hl fin hfin; omega
    simp [hnl, hb]
  · rw [hb]
    rfl

theorem decRest_ifElse {f pc p' tgt n fin : ℕ} {e : FExpr} {t s₂ : Stmt}
    (hp : parseExpr code 0 pc = some (e, p'))
    (hc : code[p']? = some (.cmp .eq (.var (temp 0)) (.imm 0) tgt n))
    (hn : code[tgt - 1]? = some (.nop fin)) (hlt : tgt < fin)
    (ht : decRegion code f (p' + 1) (tgt - 1) = some t)
    (he : decRegion code f tgt fin = some s₂) :
    decRest code f pc = some (.ifElse e t s₂, fin) := by
  simp [decRest, hp, hc, hn, hlt, ht, he]

theorem decRegion_of_decOne {s : Stmt} {f pc stop : ℕ}
    (h : decOne code f pc = some (s, stop)) : decRegion code (f + 1) pc stop = some s := by
  simp [decRegion, h]

theorem decRegion_seq {s₁ s₂ : Stmt} {f pc mid stop : ℕ}
    (h₁ : decOne code f pc = some (s₁, mid)) (hlt : mid < stop)
    (h₂ : decRegion code f mid stop = some s₂) :
    decRegion code (f + 1) pc stop = some (.seq s₁ s₂) := by
  simp [decRegion, h₁, hlt, Nat.ne_of_lt hlt, h₂]

theorem region_of_one {s : Stmt} {pc stop n : ℕ}
    (one : ∀ f, 2 * n ≤ f → decOne code f pc = some (s, stop)) :
    ∀ f, 2 * n + 1 ≤ f → decRegion code f pc stop = some s := by
  intro f hf
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  exact decRegion_of_decOne code (one g (by omega))

/-- Statements that are not sequences. -/
def NonSeq : Stmt → Prop
  | .seq _ _ => False
  | _ => True

theorem canonical_seq {s₁ s₂ : Stmt} (h : (Stmt.seq s₁ s₂).Canonical) :
    NonSeq s₁ ∧ s₁.Canonical ∧ s₂.Canonical := by
  cases s₁ with
  | seq => exact (h : False).elim
  | _ => exact ⟨trivial, h⟩

/-- The context lemma: in any code containing the compilation of a supported,
canonical statement, a region decodes to the statement, and a non-sequence
decodes in one step, with fuel linear in the length of the compiled code. -/
theorem dec_compile (s : Stmt) : s.Supported → s.Canonical → ∀ pc, At code pc (s.compile pc) →
    (∀ f, 2 * (s.compile pc).length + 1 ≤ f →
      decRegion code f pc (pc + (s.compile pc).length) = some s) ∧
    (NonSeq s → ∀ f, 2 * (s.compile pc).length ≤ f →
      decOne code f pc = some (s, pc + (s.compile pc).length)) := by
  induction s with
  | assign x e =>
    rintro ⟨-, he⟩ - pc h
    have h' : At code pc (e.compile 0 pc ++
        [.alu2 .mov x (.var (temp 0)) (pc + (e.compile 0 pc).length + 1)]) := h
    have hlen : ((Stmt.assign x e).compile pc).length = (e.compile 0 pc).length + 1 := by
      simp [Stmt.compile]
    have one : ∀ f, 2 * ((Stmt.assign x e).compile pc).length ≤ f →
        decOne code f pc = some (.assign x e, pc + ((Stmt.assign x e).compile pc).length) := by
      intro f hf
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      rw [decOne_succ_of_not_for code (not_for_of_expr h' (fun _ _ _ _ h => by cases h)),
        decRest_assign code (parseExpr_compile e he pc h'.left) (h'.right' rfl).single, hlen,
        Nat.add_assoc]
    exact ⟨region_of_one code one, fun _ => one⟩
  | forLoop x lo hi b ihb =>
    rintro ⟨hxs, -, hbs⟩ hc pc h
    have h' : At code pc ([.alu2 .mov x (.imm lo) (pc + 1), .cmp .gt (.var x) (.imm hi)
        (pc + 2 + (b.compile (pc + 2)).length + 2) (pc + 2)] ++ b.compile (pc + 2) ++
        [.alu .add x (.var x) (.imm 1) (pc + 2 + (b.compile (pc + 2)).length + 1),
          .nop (pc + 1)]) := h
    have hlen : ((Stmt.forLoop x lo hi b).compile pc).length =
        (b.compile (pc + 2)).length + 4 := by
      simp [Stmt.compile]
    have h₀ := h'.left.left.cons.1
    have h₁ := h'.left.left.cons.2.single
    have hb := (ihb hbs hc (pc + 2) (h'.left.right' (by simp))).1
    have hx : x.startsWith "%" = false := Bool.eq_false_iff.mpr hxs
    have one : ∀ f, 2 * ((Stmt.forLoop x lo hi b).compile pc).length ≤ f →
        decOne code f pc =
          some (.forLoop x lo hi b, pc + ((Stmt.forLoop x lo hi b).compile pc).length) := by
      intro f hf
      rw [hlen] at hf ⊢
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      have hbg := hb g (by omega)
      rw [show pc + 2 + (b.compile (pc + 2)).length =
        pc + 2 + (b.compile (pc + 2)).length + 2 - 2 by omega] at hbg
      rw [decOne_for code h₀ h₁ hx hbg]
      simp only [Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    exact ⟨region_of_one code one, fun _ => one⟩
  | ifThen c b ihb =>
    rintro ⟨hcs, hbs⟩ hc pc h
    have h' : At code pc (c.compile 0 pc ++
        [.cmp .eq (.var (temp 0)) (.imm 0)
          (pc + (c.compile 0 pc).length + 1 + (b.compile (pc + (c.compile 0 pc).length + 1)).length)
          (pc + (c.compile 0 pc).length + 1)] ++
        b.compile (pc + (c.compile 0 pc).length + 1)) := h
    have hlen : ((Stmt.ifThen c b).compile pc).length =
        (c.compile 0 pc).length + 1 + (b.compile (pc + (c.compile 0 pc).length + 1)).length := by
      simp [Stmt.compile]; omega
    have hbAt : At code (pc + (c.compile 0 pc).length + 1)
        (b.compile (pc + (c.compile 0 pc).length + 1)) :=
      h'.right' (by simp only [List.length_append, List.length_singleton]; omega)
    have hb := (ihb hbs hc _ hbAt).1
    obtain ⟨L, i, hL, hi⟩ := compile_last b (pc + (c.compile 0 pc).length + 1)
    have hlast : code[pc + (c.compile 0 pc).length + 1 +
        (b.compile (pc + (c.compile 0 pc).length + 1)).length - 1]? = some i := by
      have hb' := hbAt
      rw [hL] at hb'
      rw [hL, show pc + (c.compile 0 pc).length + 1 + (L ++ [i]).length - 1 =
        pc + (c.compile 0 pc).length + 1 + L.length by
          simp only [List.length_append, List.length_singleton]; omega]
      exact (hb'.right' rfl).single
    have hl : ∀ fin, code[pc + (c.compile 0 pc).length + 1 +
        (b.compile (pc + (c.compile 0 pc).length + 1)).length - 1]? = some (.nop fin) →
        fin ≤ pc + (c.compile 0 pc).length + 1 +
          (b.compile (pc + (c.compile 0 pc).length + 1)).length := by
      intro fin hfin
      rw [hlast, Option.some.injEq] at hfin
      have := hi fin hfin
      rw [hL]
      simp only [List.length_append, List.length_singleton]
      omega
    have hp := parseExpr_compile c hcs pc h'.left.left
    have hcmp := (h'.left.right' rfl).single
    have hnf := not_for_of_expr h'.left (fun _ _ _ _ h => by cases h)
    have one : ∀ f, 2 * ((Stmt.ifThen c b).compile pc).length ≤ f →
        decOne code f pc = some (.ifThen c b, pc + ((Stmt.ifThen c b).compile pc).length) := by
      intro f hf
      rw [hlen] at hf ⊢
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      rw [decOne_succ_of_not_for code hnf,
        decRest_ifThen code hp hcmp hl (hb g (by omega))]
      simp only [Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    exact ⟨region_of_one code one, fun _ => one⟩
  | ifElse c t e iht ihe =>
    rintro ⟨hcs, hts, hes⟩ ⟨hct, hce⟩ pc h
    have h' : At code pc (c.compile 0 pc ++ [.cmp .eq (.var (temp 0)) (.imm 0)
        (pc + (c.compile 0 pc).length + 1 +
          (t.compile (pc + (c.compile 0 pc).length + 1)).length + 1)
        (pc + (c.compile 0 pc).length + 1)] ++ t.compile (pc + (c.compile 0 pc).length + 1) ++
        [.nop (pc + (c.compile 0 pc).length + 1 +
          (t.compile (pc + (c.compile 0 pc).length + 1)).length + 1 +
          (e.compile (pc + (c.compile 0 pc).length + 1 +
            (t.compile (pc + (c.compile 0 pc).length + 1)).length + 1)).length)] ++
        e.compile (pc + (c.compile 0 pc).length + 1 +
          (t.compile (pc + (c.compile 0 pc).length + 1)).length + 1)) := h
    have hlen : ((Stmt.ifElse c t e).compile pc).length =
        (c.compile 0 pc).length + 1 + (t.compile (pc + (c.compile 0 pc).length + 1)).length + 1 +
          (e.compile (pc + (c.compile 0 pc).length + 1 +
            (t.compile (pc + (c.compile 0 pc).length + 1)).length + 1)).length := by
      simp [Stmt.compile]; omega
    have htAt : At code (pc + (c.compile 0 pc).length + 1)
        (t.compile (pc + (c.compile 0 pc).length + 1)) :=
      h'.left.left.right' (by simp only [List.length_append, List.length_singleton]; omega)
    have heAt : At code (pc + (c.compile 0 pc).length + 1 +
          (t.compile (pc + (c.compile 0 pc).length + 1)).length + 1)
        (e.compile (pc + (c.compile 0 pc).length + 1 +
          (t.compile (pc + (c.compile 0 pc).length + 1)).length + 1)) :=
      h'.right' (by simp only [List.length_append, List.length_singleton]; omega)
    have hn := (h'.left.right' (q := pc + (c.compile 0 pc).length + 1 +
      (t.compile (pc + (c.compile 0 pc).length + 1)).length + 1 - 1)
      (by simp only [List.length_append, List.length_singleton]; omega)).single
    have ht := (iht hts hct _ htAt).1
    have he := (ihe hes hce _ heAt).1
    have hp := parseExpr_compile c hcs pc h'.left.left.left.left
    have hcmp := (h'.left.left.left.right' rfl).single
    have hnf := not_for_of_expr h'.left.left.left (fun _ _ _ _ h => by cases h)
    have hpos := compile_length_pos e (pc + (c.compile 0 pc).length + 1 +
      (t.compile (pc + (c.compile 0 pc).length + 1)).length + 1)
    have one : ∀ f, 2 * ((Stmt.ifElse c t e).compile pc).length ≤ f →
        decOne code f pc = some (.ifElse c t e, pc + ((Stmt.ifElse c t e).compile pc).length) := by
      intro f hf
      rw [hlen] at hf ⊢
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      have htg := ht g (by omega)
      rw [show pc + (c.compile 0 pc).length + 1 +
          (t.compile (pc + (c.compile 0 pc).length + 1)).length =
        pc + (c.compile 0 pc).length + 1 +
          (t.compile (pc + (c.compile 0 pc).length + 1)).length + 1 - 1 by omega] at htg
      rw [decOne_succ_of_not_for code hnf,
        decRest_ifElse code hp hcmp hn (by omega) htg (he g (by omega))]
      simp only [Option.some.injEq, Prod.mk.injEq, true_and]
      omega
    exact ⟨region_of_one code one, fun _ => one⟩
  | seq s₁ s₂ ih₁ ih₂ =>
    rintro ⟨hs₁, hs₂⟩ hc pc h
    obtain ⟨hn₁, hc₁, hc₂⟩ := canonical_seq hc
    have h' : At code pc (s₁.compile pc ++ s₂.compile (pc + (s₁.compile pc).length)) := h
    have hlen : ((Stmt.seq s₁ s₂).compile pc).length =
        (s₁.compile pc).length + (s₂.compile (pc + (s₁.compile pc).length)).length := by
      simp [Stmt.compile]
    have h₁ := (ih₁ hs₁ hc₁ pc h'.left).2 hn₁
    have h₂ := (ih₂ hs₂ hc₂ _ h'.right).1
    have hp₁ := compile_length_pos s₁ pc
    have hp₂ := compile_length_pos s₂ (pc + (s₁.compile pc).length)
    refine ⟨fun f hf => ?_, fun h => (h : False).elim⟩
    rw [hlen] at hf ⊢
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [← Nat.add_assoc]
    exact decRegion_seq code (h₁ g (by omega)) (by omega) (h₂ g (by omega))

/-- Decompiling compiled code gives back the (supported, canonical) program. -/
theorem decompile_compile (s : Stmt) (hs : s.Supported) (hc : s.Canonical) :
    decompile (s.compile 0) = some s := by
  have hAt : At (s.compile 0) 0 (s.compile 0) := ⟨[], [], by simp, rfl⟩
  have := (dec_compile (s.compile 0) s hs hc 0 hAt).1 (2 * (s.compile 0).length + 2) (by omega)
  rw [Nat.zero_add] at this
  exact this

/-- `Decompilation.compile_injective`, derived from the decompiler: compilation
is injective on supported canonical programs. -/
theorem compile_injective_of_decompile {s s' : Stmt} (hs : s.Supported) (hs' : s'.Supported)
    (hc : s.Canonical) (hc' : s'.Canonical) (h : s.compile 0 = s'.compile 0) : s = s' := by
  have h₁ := decompile_compile s hs hc
  rw [h, decompile_compile s' hs' hc'] at h₁
  exact (Option.some.inj h₁).symm

end Silmaril.Courses.Cambridge.OptimisingCompilers.Exercises.S4Q19
