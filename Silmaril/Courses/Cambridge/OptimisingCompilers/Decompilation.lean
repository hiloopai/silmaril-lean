module

public import Silmaril.Courses.Cambridge.OptimisingCompilers.ThreeAddress
import Std.Data.String.ToNat

/-! # Part D: Decompilation and reverse engineering (notes pp. 39–41;
slides pp. 127–131)

"Extracting the flowgraph from an assembler program is easy. The trick is then
to match intervals of the flowgraph with higher-level control structures, e.g.
loops, if-then-else" (notes p. 40).

The development uses the structured language *farboo* of exercise sheet 4
(questions 18–19):

```
statements ::= statement statements | statement
statement  ::= for var = N to N do statements end
             | if expr then statements end
             | if expr then statements else statements end
             | var = expr
expr       ::= val operator expr | val
```

* `Stmt.run` is its semantics (`if` tests non-zero, as in C);
* `compile` translates it to the course's 3-address code, with absolute labels,
  computing expressions into temporaries `%0, %1, …` as in the sheet's code;
* `compile_correct`: the compiled flowgraph halts with the program's final
  values in every non-temporary variable;
* `compile_injective`: compilation loses no structure, so decompilation of
  compiled code is well defined. Exercise S4Q19 gives the decompiler.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers.Decompilation

/-- `val ::= N | var`. -/
inductive Val where
  | num (n : ℤ)
  | var (x : String)
  deriving DecidableEq

/-- `operator ::= + | − | ∗ | \` (the last read as integer division). -/
inductive Op where
  | add | sub | mul | div
  deriving DecidableEq

/-- `expr ::= val operator expr | val`. -/
inductive FExpr where
  | val (v : Val)
  | op (v : Val) (o : Op) (e : FExpr)
  deriving DecidableEq

/-- Statements; `seq` is `statement statements`. -/
inductive Stmt where
  | assign (x : String) (e : FExpr)
  | forLoop (x : String) (lo hi : ℤ) (body : Stmt)
  | ifThen (c : FExpr) (body : Stmt)
  | ifElse (c : FExpr) (t e : Stmt)
  | seq (s₁ s₂ : Stmt)
  deriving DecidableEq

abbrev FEnv := String → ℤ

def Val.eval (env : FEnv) : Val → ℤ
  | .num n => n
  | .var x => env x

def Op.eval : Op → ℤ → ℤ → ℤ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b

def FExpr.eval (env : FEnv) : FExpr → ℤ
  | .val v => v.eval env
  | .op v o e => o.eval (v.eval env) (e.eval env)

/-- Semantics. `for x = lo to hi` runs the body for `x = lo, …, hi` and leaves
`x` one past the last value, as the C-style compiled loop does (the body may
not assign `x`, see `Stmt.Supported`). -/
def Stmt.run : Stmt → FEnv → FEnv
  | .assign x e, env => Function.update env x (e.eval env)
  | .forLoop x lo hi body, env =>
    let env' := (List.range (hi - lo + 1).toNat).foldl
      (fun env k => body.run (Function.update env x (lo + k))) env
    Function.update env' x (max lo (hi + 1))
  | .ifThen c body, env => if c.eval env ≠ 0 then body.run env else env
  | .ifElse c t e, env => if c.eval env ≠ 0 then t.run env else e.run env
  | .seq s₁ s₂, env => s₂.run (s₁.run env)

/-! ## Compilation to 3-address code -/

/-- Temporaries `%k`. -/
def temp (k : ℕ) : String := "%" ++ toString k

/-- Program variables never start with `%`. -/
def IsTemp (x : String) : Prop := x.startsWith "%" = true

def Val.toOperand : Val → Operand String
  | .num n => .imm n
  | .var x => .var x

def Op.toAlu : Op → Option AluOp
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul
  | .div => none

/-- Compile an expression into temporary `%k` (using `%k+1, …` for
subexpressions), starting at label `pc`. The IR has no division, so `Op.div`
is excluded by `FExpr.Supported`. -/
def FExpr.compile (k pc : ℕ) : FExpr → List (Instr String ℕ)
  | .val v => [.alu2 .mov (temp k) v.toOperand (pc + 1)]
  | .op v o e =>
    let ce := e.compile (k + 1) pc
    ce ++ [.alu ((o.toAlu).getD .add) (temp k) v.toOperand (.var (temp (k + 1))) (pc + ce.length + 1)]

/-- Values mention no temporaries. -/
def Val.Supported : Val → Prop
  | .num _ => True
  | .var x => ¬ IsTemp x

/-- Expressions avoid division and temporaries. -/
def FExpr.Supported : FExpr → Prop
  | .val v => v.Supported
  | .op v o e => v.Supported ∧ o ≠ .div ∧ e.Supported

/-- The variables a statement assigns. -/
def Stmt.Assigns : Stmt → String → Prop
  | .assign x _, y => x = y
  | .forLoop x _ _ b, y => x = y ∨ b.Assigns y
  | .ifThen _ b, y => b.Assigns y
  | .ifElse _ t e, y => t.Assigns y ∨ e.Assigns y
  | .seq s₁ s₂, y => s₁.Assigns y ∨ s₂.Assigns y

/-- Statements avoid division and temporaries, and loop bodies do not assign
their loop variable. -/
def Stmt.Supported : Stmt → Prop
  | .assign x e => ¬ IsTemp x ∧ e.Supported
  | .forLoop x _ _ b => ¬ IsTemp x ∧ ¬ b.Assigns x ∧ b.Supported
  | .ifThen c b => c.Supported ∧ b.Supported
  | .ifElse c t e => c.Supported ∧ t.Supported ∧ e.Supported
  | .seq s₁ s₂ => s₁.Supported ∧ s₂.Supported

/-- Canonical form: sequences nest to the right ("statement statements"). -/
def Stmt.Canonical : Stmt → Prop
  | .assign _ _ => True
  | .forLoop _ _ _ b => b.Canonical
  | .ifThen _ b => b.Canonical
  | .ifElse _ t e => t.Canonical ∧ e.Canonical
  | .seq (.seq _ _) _ => False
  | .seq s₁ s₂ => s₁.Canonical ∧ s₂.Canonical

/-- Compile a statement starting at label `pc`; control falls through to label
`pc + length`. -/
def Stmt.compile : Stmt → ℕ → List (Instr String ℕ)
  | .assign x e, pc =>
    let ce := e.compile 0 pc
    ce ++ [.alu2 .mov x (.var (temp 0)) (pc + ce.length + 1)]
  | .forLoop x lo hi body, pc =>
    -- pc: MOV x, #lo; pc+1: CMPGT x, #hi → end / pc+2; body; ADD x, x, #1; B pc+1
    let cb := body.compile (pc + 2)
    let stop := pc + 2 + cb.length + 2
    [.alu2 .mov x (.imm lo) (pc + 1), .cmp .gt (.var x) (.imm hi) stop (pc + 2)] ++ cb ++
      [.alu .add x (.var x) (.imm 1) (pc + 2 + cb.length + 1), .nop (pc + 1)]
  | .ifThen c body, pc =>
    let cc := c.compile 0 pc
    let cb := body.compile (pc + cc.length + 1)
    cc ++ [.cmp .eq (.var (temp 0)) (.imm 0) (pc + cc.length + 1 + cb.length)
      (pc + cc.length + 1)] ++ cb
  | .ifElse c t e, pc =>
    let cc := c.compile 0 pc
    let ct := t.compile (pc + cc.length + 1)
    let ce := e.compile (pc + cc.length + 1 + ct.length + 1)
    cc ++ [.cmp .eq (.var (temp 0)) (.imm 0) (pc + cc.length + 1 + ct.length + 1)
      (pc + cc.length + 1)] ++ ct ++
      [.nop (pc + cc.length + 1 + ct.length + 1 + ce.length)] ++ ce
  | .seq s₁ s₂, pc =>
    let c₁ := s₁.compile pc
    c₁ ++ s₂.compile (pc + c₁.length)

/-- The flowgraph of a code list: label `n` is the `n`th instruction, and labels
past the end exit. -/
def toFlowgraph (code : List (Instr String ℕ)) : Flowgraph String ℕ where
  entry := 0
  code n := code.getD n (.exit [])

/-! ## Temporaries -/

/-- Arithmetic on code labels and list lengths. -/
local macro "len_arith" : tactic =>
  `(tactic| first
    | omega
    | (simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    | simp
    | (simp; omega))

theorem isTemp_temp (k : ℕ) : IsTemp (temp k) := by
  unfold IsTemp temp
  rw [String.startsWith_string_iff, String.toList_append]
  exact List.prefix_append _ _

theorem ne_temp_of_not_isTemp {x : String} (hx : ¬ IsTemp x) (k : ℕ) : x ≠ temp k :=
  fun h => hx (h ▸ isTemp_temp k)

theorem temp_injective : Function.Injective temp := by
  intro a b h
  unfold temp at h
  rw [String.append_right_inj] at h
  exact Nat.repr_injective h

/-! ## Execution helpers -/

section Exec

variable (G : Flowgraph String ℕ)

theorem steps_trans {a b c : Config String ℕ} {w₁ w₂ : List ℤ} (h₁ : G.Steps a w₁ b)
    (h₂ : G.Steps b w₂ c) : G.Steps a (w₁ ++ w₂) c := by
  induction h₁ with
  | refl => exact h₂
  | head hs _ ih => rw [List.append_assoc]; exact .head hs (ih h₂)

/-- Silent runs compose. -/
theorem steps_silent {a b c : Config String ℕ} (h₁ : G.Steps a [] b) (h₂ : G.Steps b [] c) :
    G.Steps a [] c :=
  steps_trans G h₁ h₂

theorem steps_pc_eq {a : Config String ℕ} {p q : ℕ} {e : Env String} {m : Mem}
    (h : G.Steps a [] ⟨p, e, m⟩) (hpq : p = q) : G.Steps a [] ⟨q, e, m⟩ := hpq ▸ h

theorem code_eq {p q : ℕ} {i : Instr String ℕ} (h : G.code p = i) (hpq : p = q) :
    G.code q = i := hpq ▸ h

theorem steps_of_step {a b : Config String ℕ} (h : G.step a = some (none, b)) :
    G.Steps a [] b :=
  .head (o := none) h (.refl b)

variable {G}

theorem step_nop {p n : ℕ} {env : Env String} {mem : Mem} (h : G.code p = .nop n) :
    G.Steps ⟨p, env, mem⟩ [] ⟨n, env, mem⟩ :=
  steps_of_step G (by show ((G.code p).exec env mem).map _ = _; rw [h]; rfl)

theorem step_alu2 {p n : ℕ} {op : UnOp} {d : String} {a : Operand String} {env : Env String}
    {mem : Mem} (h : G.code p = .alu2 op d a n) :
    G.Steps ⟨p, env, mem⟩ [] ⟨n, Function.update env d (op.eval (a.eval env)), mem⟩ :=
  steps_of_step G (by show ((G.code p).exec env mem).map _ = _; rw [h]; rfl)

theorem step_alu {p n : ℕ} {op : AluOp} {d : String} {a b : Operand String}
    {env : Env String} {mem : Mem} (h : G.code p = .alu op d a b n) :
    G.Steps ⟨p, env, mem⟩ [] ⟨n, Function.update env d (op.eval (a.eval env) (b.eval env)), mem⟩ :=
  steps_of_step G (by show ((G.code p).exec env mem).map _ = _; rw [h]; rfl)

theorem step_cmp_true {p t f : ℕ} {c : Cond} {a b : Operand String} {env : Env String}
    {mem : Mem} (h : G.code p = .cmp c a b t f) (hc : c.eval (a.eval env) (b.eval env) = true) :
    G.Steps ⟨p, env, mem⟩ [] ⟨t, env, mem⟩ :=
  steps_of_step G (by show ((G.code p).exec env mem).map _ = _; rw [h]; simp [Instr.exec, hc])

theorem step_cmp_false {p t f : ℕ} {c : Cond} {a b : Operand String} {env : Env String}
    {mem : Mem} (h : G.code p = .cmp c a b t f) (hc : c.eval (a.eval env) (b.eval env) = false) :
    G.Steps ⟨p, env, mem⟩ [] ⟨f, env, mem⟩ :=
  steps_of_step G (by show ((G.code p).exec env mem).map _ = _; rw [h]; simp [Instr.exec, hc])

end Exec

/-- `l` is laid out in `G` from label `pc` on. -/
def CodeAt (G : Flowgraph String ℕ) (pc : ℕ) (l : List (Instr String ℕ)) : Prop :=
  ∀ i (hi : i < l.length), G.code (pc + i) = l[i]

section CodeAt

variable {G : Flowgraph String ℕ}

theorem codeAt_append {pc : ℕ} {l₁ l₂ : List (Instr String ℕ)} :
    CodeAt G pc (l₁ ++ l₂) ↔ CodeAt G pc l₁ ∧ CodeAt G (pc + l₁.length) l₂ := by
  unfold CodeAt
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [h i (by len_arith), List.getElem_append_left hi]
    · rw [Nat.add_assoc, h (l₁.length + i) (by len_arith),
        List.getElem_append_right (by omega)]
      simp
  · rintro ⟨h₁, h₂⟩ i hi
    by_cases hi' : i < l₁.length
    · rw [h₁ i hi', List.getElem_append_left hi']
    · rw [List.getElem_append_right (by omega)]
      have := h₂ (i - l₁.length) (by simp at hi; omega)
      rw [show pc + l₁.length + (i - l₁.length) = pc + i by omega] at this
      exact this

theorem codeAt_nil {pc : ℕ} : CodeAt G pc [] ↔ True :=
  ⟨fun _ => trivial, fun _ i hi => absurd hi (by simp)⟩

theorem codeAt_cons {pc : ℕ} {a : Instr String ℕ} {l : List (Instr String ℕ)} :
    CodeAt G pc (a :: l) ↔ G.code pc = a ∧ CodeAt G (pc + 1) l := by
  rw [show a :: l = [a] ++ l from rfl, codeAt_append]
  refine and_congr ⟨fun h => by simpa using h 0 (by simp), fun h i hi => ?_⟩ Iff.rfl
  have : i = 0 := by simp at hi; omega
  subst this
  simpa using h

theorem codeAt_pc_eq {p q : ℕ} {l : List (Instr String ℕ)} (h : CodeAt G p l) (hpq : p = q) :
    CodeAt G q l := hpq ▸ h

end CodeAt

/-! ## Evaluation lemmas -/

theorem Val.eval_toOperand (v : Val) (env : FEnv) : v.toOperand.eval env = v.eval env := by
  cases v <;> rfl

theorem Val.eval_congr {v : Val} (hv : v.Supported) {env σ : FEnv}
    (h : ∀ z, ¬ IsTemp z → env z = σ z) : v.eval env = v.eval σ := by
  cases v with
  | num n => rfl
  | var x => exact h x hv

theorem FExpr.eval_congr {e : FExpr} (he : e.Supported) {env σ : FEnv}
    (h : ∀ z, ¬ IsTemp z → env z = σ z) : e.eval env = e.eval σ := by
  induction e with
  | val v => exact Val.eval_congr he h
  | op v o e ih =>
    simp only [FExpr.Supported] at he
    show o.eval (v.eval env) (e.eval env) = o.eval (v.eval σ) (e.eval σ)
    rw [Val.eval_congr he.1 h, ih he.2.2]

theorem Op.eval_toAlu {o : Op} (ho : o ≠ .div) (a b : ℤ) :
    ((o.toAlu).getD .add).eval a b = o.eval a b := by
  cases o <;> first | rfl | exact absurd rfl ho

theorem Val.toOperand_injective : Function.Injective Val.toOperand := by
  intro a b h
  cases a <;> cases b <;> simp_all [Val.toOperand]

theorem Op.toAlu_getD_injective {o o' : Op} (ho : o ≠ .div) (ho' : o' ≠ .div)
    (h : (o.toAlu).getD .add = (o'.toAlu).getD .add) : o = o' := by
  cases o <;> cases o' <;> simp_all [Op.toAlu]

/-! ## Semantic lemmas -/

/-- The environment after `k` iterations of a `for` loop. -/
def loopEnv (x : String) (lo : ℤ) (b : Stmt) (σ : FEnv) (k : ℕ) : FEnv :=
  (List.range k).foldl (fun env j => b.run (Function.update env x (lo + j))) σ

theorem loopEnv_zero (x : String) (lo : ℤ) (b : Stmt) (σ : FEnv) : loopEnv x lo b σ 0 = σ := by
  simp [loopEnv]

theorem loopEnv_succ (x : String) (lo : ℤ) (b : Stmt) (σ : FEnv) (k : ℕ) :
    loopEnv x lo b σ (k + 1) = b.run (Function.update (loopEnv x lo b σ k) x (lo + k)) := by
  simp [loopEnv, List.range_succ, List.foldl_append]

theorem Stmt.run_forLoop (x : String) (lo hi : ℤ) (b : Stmt) (σ : FEnv) :
    (Stmt.forLoop x lo hi b).run σ =
      Function.update (loopEnv x lo b σ (hi - lo + 1).toNat) x (max lo (hi + 1)) := rfl

/-- A statement leaves the variables it does not assign unchanged. -/
theorem Stmt.run_of_not_assigns (s : Stmt) {y : String} (h : ¬ s.Assigns y) :
    ∀ σ : FEnv, s.run σ y = σ y := by
  induction s with
  | assign x e =>
    intro σ
    exact Function.update_of_ne (fun e => h e.symm) _ _
  | forLoop x lo hi b ih =>
    simp only [Stmt.Assigns, not_or] at h
    intro σ
    rw [Stmt.run_forLoop, Function.update_of_ne (fun e => h.1 e.symm)]
    induction (hi - lo + 1).toNat with
    | zero => rw [loopEnv_zero]
    | succ k ihk =>
      rw [loopEnv_succ, ih h.2, Function.update_of_ne (fun e => h.1 e.symm), ihk]
  | ifThen c b ih =>
    intro σ
    simp only [Stmt.run]
    split_ifs
    · exact ih h σ
    · rfl
  | ifElse c t e iht ihe =>
    simp only [Stmt.Assigns, not_or] at h
    intro σ
    simp only [Stmt.run]
    split_ifs
    · exact iht h.1 σ
    · exact ihe h.2 σ
  | seq s₁ s₂ ih₁ ih₂ =>
    simp only [Stmt.Assigns, not_or] at h
    intro σ
    simp only [Stmt.run]
    rw [ih₂ h.2, ih₁ h.1]

/-! ## Correctness of compilation -/

/-- Expression code computes the expression into `%k`, leaving program
variables unchanged. -/
theorem FExpr.compile_run (G : Flowgraph String ℕ) (e : FExpr) (he : e.Supported) (k pc : ℕ)
    (hc : CodeAt G pc (e.compile k pc)) (env : Env String) (mem : Mem) :
    ∃ env', G.Steps ⟨pc, env, mem⟩ [] ⟨pc + (e.compile k pc).length, env', mem⟩ ∧
      env' (temp k) = e.eval env ∧ ∀ z, ¬ IsTemp z → env' z = env z := by
  induction e generalizing k with
  | val v =>
    simp only [FExpr.compile] at hc ⊢
    rw [codeAt_cons] at hc
    refine ⟨Function.update env (temp k) (UnOp.mov.eval (v.toOperand.eval env)),
      steps_pc_eq G (step_alu2 hc.1) (by len_arith), ?_, ?_⟩
    · rw [Function.update_self]
      exact Val.eval_toOperand v env
    · intro z hz
      exact Function.update_of_ne (ne_temp_of_not_isTemp hz k) _ _
  | op v o e ih =>
    simp only [FExpr.Supported] at he
    simp only [FExpr.compile] at hc ⊢
    rw [codeAt_append, codeAt_cons] at hc
    obtain ⟨hc1, hc2, -⟩ := hc
    obtain ⟨env1, hs1, ht1, hn1⟩ := ih he.2.2 (k + 1) hc1
    refine ⟨Function.update env1 (temp k) (((o.toAlu).getD .add).eval (v.toOperand.eval env1)
        ((Operand.var (temp (k + 1))).eval env1)),
      steps_silent G hs1 (steps_pc_eq G (step_alu hc2) (by len_arith)), ?_, ?_⟩
    · rw [Function.update_self, Op.eval_toAlu he.2.1, Val.eval_toOperand]
      show o.eval (v.eval env1) (env1 (temp (k + 1))) = o.eval (v.eval env) (e.eval env)
      rw [ht1, Val.eval_congr he.1 hn1]
    · intro z hz
      rw [Function.update_of_ne (ne_temp_of_not_isTemp hz k)]
      exact hn1 z hz

/-- Statement code, laid out anywhere in a flowgraph, runs silently to its end,
agreeing with the source semantics on program variables. -/
theorem Stmt.compile_run (G : Flowgraph String ℕ) (s : Stmt) : s.Supported → ∀ pc : ℕ,
    CodeAt G pc (s.compile pc) → ∀ (env σ : Env String) (mem : Mem),
    (∀ z, ¬ IsTemp z → env z = σ z) →
    ∃ env', G.Steps ⟨pc, env, mem⟩ [] ⟨pc + (s.compile pc).length, env', mem⟩ ∧
      ∀ z, ¬ IsTemp z → env' z = s.run σ z := by
  induction s with
  | assign x e =>
    intro hs pc hc env σ mem hag
    simp only [Stmt.Supported] at hs
    simp only [Stmt.compile] at hc ⊢
    rw [codeAt_append, codeAt_cons] at hc
    obtain ⟨hc1, hc2, -⟩ := hc
    obtain ⟨env1, hs1, ht1, hn1⟩ := FExpr.compile_run G e hs.2 0 pc hc1 env mem
    refine ⟨Function.update env1 x (UnOp.mov.eval ((Operand.var (temp 0)).eval env1)),
      steps_silent G hs1 (steps_pc_eq G (step_alu2 hc2) (by len_arith)), ?_⟩
    intro z hz
    simp only [Stmt.run]
    by_cases hzx : z = x
    · rw [hzx, Function.update_self, Function.update_self]
      show env1 (temp 0) = _
      rw [ht1]
      exact FExpr.eval_congr hs.2 hag
    · rw [Function.update_of_ne hzx, Function.update_of_ne hzx, hn1 z hz, hag z hz]
  | forLoop x lo hi b ih =>
    intro hs pc hc env σ mem hag
    simp only [Stmt.Supported] at hs
    obtain ⟨hx, hbx, hb⟩ := hs
    simp only [Stmt.compile] at hc ⊢
    simp only [codeAt_append, codeAt_cons, codeAt_nil, and_true] at hc
    obtain ⟨⟨⟨hc1, hc2⟩, hc3⟩, hc4, hc5⟩ := hc
    have hc3' : CodeAt G (pc + 2) (b.compile (pc + 2)) := codeAt_pc_eq hc3 (by len_arith)
    have hc4' : G.code (pc + 2 + (b.compile (pc + 2)).length) = _ := code_eq G hc4 (by len_arith)
    have hc5' : G.code (pc + 2 + (b.compile (pc + 2)).length + 1) = _ :=
      code_eq G hc5 (by len_arith)
    obtain ⟨N, hN⟩ : ∃ N, N = (hi - lo + 1).toNat := ⟨_, rfl⟩
    -- the loop, from its test at `pc + 1`
    have loop : ∀ m k (e : Env String), m = N - k → k ≤ N → e x = lo + k →
        (∀ z, ¬ IsTemp z → e z = Function.update (loopEnv x lo b σ k) x (lo + k) z) →
        ∃ env', G.Steps ⟨pc + 1, e, mem⟩ [] ⟨pc + 2 + (b.compile (pc + 2)).length + 2, env', mem⟩ ∧
          ∀ z, ¬ IsTemp z → env' z = Function.update (loopEnv x lo b σ N) x (lo + N) z := by
      intro m
      induction m with
      | zero =>
        intro k e hm hk hex hag'
        obtain rfl : k = N := by omega
        refine ⟨e, step_cmp_true hc2 ?_, hag'⟩
        simp only [Cond.eval, Operand.eval, hex, decide_eq_true_eq]
        omega
      | succ m ihm =>
        intro k e hm hk hex hag'
        have hlt : (k : ℤ) < N := by omega
        obtain ⟨env1, hs1, hn1⟩ := ih hb (pc + 2) hc3' e
          (Function.update (loopEnv x lo b σ k) x (lo + k)) mem hag'
        have hx1 : env1 x = lo + k := by
          rw [hn1 x hx, Stmt.run_of_not_assigns b hbx, Function.update_self]
        obtain ⟨env', hs', hn'⟩ := ihm (k + 1)
          (Function.update env1 x (AluOp.add.eval ((Operand.var x).eval env1)
            ((Operand.imm 1).eval env1))) (by omega) (by omega)
          (by rw [Function.update_self]; show env1 x + 1 = _; rw [hx1]; omega)
          (by
            intro z hz
            by_cases hzx : z = x
            · rw [hzx, Function.update_self, Function.update_self]
              show env1 x + 1 = _
              rw [hx1]; omega
            · rw [Function.update_of_ne hzx, Function.update_of_ne hzx, hn1 z hz,
                loopEnv_succ])
        refine ⟨env', steps_silent G (step_cmp_false hc2 ?_) (steps_silent G hs1
          (steps_silent G (step_alu hc4') (steps_silent G (step_nop hc5') hs'))), hn'⟩
        simp only [Cond.eval, Operand.eval, hex, decide_eq_false_iff_not]
        omega
    obtain ⟨env', hs', hn'⟩ := loop (N - 0) 0
      (Function.update env x (UnOp.mov.eval ((Operand.imm lo).eval env))) rfl (by omega)
      (by rw [Function.update_self]; simp [UnOp.eval, Operand.eval])
      (by
        intro z hz
        by_cases hzx : z = x
        · rw [hzx, Function.update_self, Function.update_self]
          simp [UnOp.eval, Operand.eval]
        · rw [Function.update_of_ne hzx, Function.update_of_ne hzx, loopEnv_zero, hag z hz])
    refine ⟨env', steps_silent G (step_alu2 hc1) (steps_pc_eq G hs' (by len_arith)), ?_⟩
    have hmax : max lo (hi + 1) = lo + (N : ℤ) := by
      rw [max_def]; split_ifs <;> omega
    intro z hz
    rw [hn' z hz, Stmt.run_forLoop, ← hN, hmax]
  | ifThen c b ih =>
    intro hs pc hc env σ mem hag
    simp only [Stmt.Supported] at hs
    simp only [Stmt.compile] at hc ⊢
    rw [codeAt_append, codeAt_append, codeAt_cons] at hc
    obtain ⟨⟨hc1, hc2, -⟩, hc3⟩ := hc
    have hc3' : CodeAt G (pc + (c.compile 0 pc).length + 1)
        (b.compile (pc + (c.compile 0 pc).length + 1)) := codeAt_pc_eq hc3 (by len_arith)
    obtain ⟨env1, hs1, ht1, hn1⟩ := FExpr.compile_run G c hs.1 0 pc hc1 env mem
    have hceq : c.eval env = c.eval σ := FExpr.eval_congr hs.1 hag
    have hag1 : ∀ z, ¬ IsTemp z → env1 z = σ z := fun z hz => (hn1 z hz).trans (hag z hz)
    by_cases hz : c.eval σ = 0
    · refine ⟨env1, steps_silent G hs1 (steps_pc_eq G (step_cmp_true hc2 ?_) (by len_arith)), ?_⟩
      · simp [Cond.eval, Operand.eval, ht1, hceq, hz]
      · intro z hz'
        rw [hag1 z hz']
        simp [Stmt.run, hz]
    · obtain ⟨env2, hs2, hn2⟩ := ih hs.2 _ hc3' env1 σ mem hag1
      refine ⟨env2, steps_silent G hs1 (steps_silent G (step_cmp_false hc2 ?_)
        (steps_pc_eq G hs2 (by len_arith))), ?_⟩
      · simp [Cond.eval, Operand.eval, ht1, hceq, hz]
      · intro z hz'
        rw [hn2 z hz']
        simp [Stmt.run, hz]
  | ifElse c t e iht ihe =>
    intro hs pc hc env σ mem hag
    simp only [Stmt.Supported] at hs
    obtain ⟨hcs, hts, hes⟩ := hs
    simp only [Stmt.compile] at hc ⊢
    simp only [codeAt_append, codeAt_cons, codeAt_nil, and_true] at hc
    obtain ⟨⟨⟨⟨hc1, hc2⟩, hc3⟩, hc4⟩, hc5⟩ := hc
    have hc3' : CodeAt G (pc + (c.compile 0 pc).length + 1)
        (t.compile (pc + (c.compile 0 pc).length + 1)) := codeAt_pc_eq hc3 (by len_arith)
    have hc4' : G.code (pc + (c.compile 0 pc).length + 1 +
        (t.compile (pc + (c.compile 0 pc).length + 1)).length) = _ := code_eq G hc4 (by len_arith)
    have hc5' : CodeAt G (pc + (c.compile 0 pc).length + 1 +
        (t.compile (pc + (c.compile 0 pc).length + 1)).length + 1)
        (e.compile (pc + (c.compile 0 pc).length + 1 +
          (t.compile (pc + (c.compile 0 pc).length + 1)).length + 1)) :=
      codeAt_pc_eq hc5 (by len_arith)
    obtain ⟨env1, hs1, ht1, hn1⟩ := FExpr.compile_run G c hcs 0 pc hc1 env mem
    have hceq : c.eval env = c.eval σ := FExpr.eval_congr hcs hag
    have hag1 : ∀ z, ¬ IsTemp z → env1 z = σ z := fun z hz => (hn1 z hz).trans (hag z hz)
    by_cases hz : c.eval σ = 0
    · obtain ⟨env2, hs2, hn2⟩ := ihe hes _ hc5' env1 σ mem hag1
      refine ⟨env2, steps_silent G hs1 (steps_silent G (step_cmp_true hc2 ?_)
        (steps_pc_eq G hs2 (by len_arith))), ?_⟩
      · simp [Cond.eval, Operand.eval, ht1, hceq, hz]
      · intro z hz'
        rw [hn2 z hz']
        simp [Stmt.run, hz]
    · obtain ⟨env2, hs2, hn2⟩ := iht hts _ hc3' env1 σ mem hag1
      refine ⟨env2, steps_silent G hs1 (steps_silent G (step_cmp_false hc2 ?_)
        (steps_silent G hs2 (steps_pc_eq G (step_nop hc4') (by len_arith)))), ?_⟩
      · simp [Cond.eval, Operand.eval, ht1, hceq, hz]
      · intro z hz'
        rw [hn2 z hz']
        simp [Stmt.run, hz]
  | seq s₁ s₂ ih₁ ih₂ =>
    intro hs pc hc env σ mem hag
    simp only [Stmt.Supported] at hs
    simp only [Stmt.compile] at hc ⊢
    rw [codeAt_append] at hc
    obtain ⟨env1, hs1, hn1⟩ := ih₁ hs.1 pc hc.1 env σ mem hag
    obtain ⟨env2, hs2, hn2⟩ := ih₂ hs.2 _ hc.2 env1 (s₁.run σ) mem hn1
    refine ⟨env2, steps_silent G hs1 (steps_pc_eq G hs2 (by len_arith)), ?_⟩
    exact hn2

/-- Compilation is correct: the compiled code halts, agreeing with the program
on every non-temporary variable. -/
theorem compile_correct (s : Stmt) (hs : s.Supported) (env : Env String) (mem : Mem) :
    ∃ t : Config String ℕ, (toFlowgraph (s.compile 0)).Steps ⟨0, env, mem⟩ [] t ∧
      (toFlowgraph (s.compile 0)).Halted t ∧ ∀ x, ¬ IsTemp x → t.env x = s.run env x := by
  have hcode : CodeAt (toFlowgraph (s.compile 0)) 0 (s.compile 0) := fun i hi => by
    show (s.compile 0).getD (0 + i) (.exit []) = _
    simp [List.getD_eq_getElem?_getD, hi]
  obtain ⟨env', hsteps, hag⟩ :=
    Stmt.compile_run (toFlowgraph (s.compile 0)) s hs 0 hcode env env mem (fun _ _ => rfl)
  refine ⟨_, hsteps, ⟨[], ?_⟩, hag⟩
  show (s.compile 0).getD (0 + (s.compile 0).length) (.exit []) = _
  simp [List.getD_eq_getElem?_getD]

/-! ## Injectivity of compilation -/

/-- Sequences. -/
def Stmt.IsSeq : Stmt → Prop
  | .seq _ _ => True
  | _ => False

theorem Stmt.canonical_seq (a b : Stmt) :
    (Stmt.seq a b).Canonical ↔ ¬ a.IsSeq ∧ a.Canonical ∧ b.Canonical := by
  cases a <;> simp [Stmt.Canonical, Stmt.IsSeq]

theorem Stmt.compile_ne_nil (s : Stmt) (pc : ℕ) : s.compile pc ≠ [] := by
  induction s generalizing pc <;> simp [Stmt.compile, *]

theorem head_eq_of_append_eq {α : Type*} {l l' r r' : List α} {a a' : α}
    (h : l ++ r = l' ++ r') (hl : l.head? = some a) (hl' : l'.head? = some a') : a = a' := by
  have := congrArg List.head? h
  rw [List.head?_append, List.head?_append, hl, hl'] at this
  simpa using this

theorem FExpr.compile_head (e : FExpr) (k pc : ℕ) :
    ∃ j v, (e.compile k pc).head? = some (.alu2 .mov (temp (k + j)) v (pc + 1)) := by
  induction e generalizing k with
  | val v => exact ⟨0, v.toOperand, rfl⟩
  | op v o e ih =>
    obtain ⟨j, w, h⟩ := ih (k + 1)
    refine ⟨j + 1, w, ?_⟩
    rw [show k + (j + 1) = k + 1 + j by omega]
    simp only [FExpr.compile]
    rw [List.head?_append, h]
    rfl

/-- A `MOV` into a program variable is not the start of expression code. -/
theorem mov_cons_ne_expr {x : String} (hx : ¬ IsTemp x) {o : Operand String} {n : ℕ}
    {L R : List (Instr String ℕ)} (c : FExpr) (k pc : ℕ) :
    Instr.alu2 .mov x o n :: L ≠ c.compile k pc ++ R := by
  intro h
  obtain ⟨j, v, hj⟩ := FExpr.compile_head c k pc
  have h2 := head_eq_of_append_eq (l := [Instr.alu2 .mov x o n]) (r := L) h rfl hj
  obtain ⟨-, hxt, -, -⟩ := Instr.alu2.inj h2
  exact ne_temp_of_not_isTemp hx _ hxt

/-- Expression code is prefix-free and injective. -/
theorem FExpr.compile_prefix_aux (e : FExpr) : ∀ (e' : FExpr) (k pc : ℕ)
    (r r' : List (Instr String ℕ)), e.Supported → e'.Supported →
    e.compile k pc ++ r = e'.compile k pc ++ r' → e = e' ∧ r = r' := by
  induction e with
  | val v =>
    intro e' k pc r r' _ he' h
    cases e' with
    | val v' =>
      simp only [FExpr.compile, List.singleton_append] at h
      obtain ⟨hI, hr⟩ := List.cons.inj h
      obtain ⟨-, -, hv, -⟩ := Instr.alu2.inj hI
      exact ⟨by rw [Val.toOperand_injective hv], hr⟩
    | op v' o' e'' =>
      exfalso
      simp only [FExpr.compile, List.append_assoc] at h
      obtain ⟨j, w, hj⟩ := FExpr.compile_head e'' (k + 1) pc
      have h2 := head_eq_of_append_eq h rfl hj
      obtain ⟨-, ht, -, -⟩ := Instr.alu2.inj h2
      have := temp_injective ht
      omega
  | op v o e ih =>
    intro e' k pc r r' he he' h
    simp only [FExpr.Supported] at he
    cases e' with
    | val v' =>
      exfalso
      simp only [FExpr.compile, List.append_assoc] at h
      obtain ⟨j, w, hj⟩ := FExpr.compile_head e (k + 1) pc
      have h2 := head_eq_of_append_eq h.symm rfl hj
      obtain ⟨-, ht, -, -⟩ := Instr.alu2.inj h2
      have := temp_injective ht
      omega
    | op v' o' e'' =>
      simp only [FExpr.Supported] at he'
      simp only [FExpr.compile, List.append_assoc] at h
      obtain ⟨rfl, h2⟩ := ih _ _ _ _ _ he.2.2 he'.2.2 h
      rw [List.singleton_append, List.singleton_append] at h2
      obtain ⟨hA, hr⟩ := List.cons.inj h2
      obtain ⟨hop, -, hv, -, -⟩ := Instr.alu.inj hA
      obtain rfl := Val.toOperand_injective hv
      obtain rfl := Op.toAlu_getD_injective he.2.1 he'.2.1 hop
      exact ⟨rfl, hr⟩

/-- Expression code is prefix-free and injective. -/
theorem FExpr.compile_prefix {e e' : FExpr} (he : e.Supported) (he' : e'.Supported) {k pc : ℕ}
    {r r' : List (Instr String ℕ)} (h : e.compile k pc ++ r = e'.compile k pc ++ r') :
    e = e' ∧ r = r' :=
  FExpr.compile_prefix_aux e e' k pc r r' he he' h

/-- The last instruction of statement code is never a forward `NOP` past its
end. -/
theorem Stmt.compile_last_nop (s : Stmt) (pc t : ℕ)
    (h : (s.compile pc).getLast? = some (.nop t)) : t < pc + (s.compile pc).length := by
  induction s generalizing pc with
  | assign x e => simp [Stmt.compile] at h
  | forLoop x lo hi b ih =>
    simp only [Stmt.compile] at h ⊢
    rw [List.getLast?_append] at h
    have h' : (Instr.nop (pc + 1) : Instr String ℕ) = .nop t := Option.some.inj h
    injection h' with h''
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  | ifThen c b ih =>
    simp only [Stmt.compile] at h ⊢
    rw [List.getLast?_append] at h
    cases hb : (b.compile (pc + (c.compile 0 pc).length + 1)).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hb) (Stmt.compile_ne_nil _ _)
    | some y =>
      rw [hb] at h
      have := ih _ (hb.trans h)
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  | ifElse c t' e iht ihe =>
    simp only [Stmt.compile] at h ⊢
    rw [List.getLast?_append] at h
    cases hb : (e.compile (pc + (c.compile 0 pc).length + 1 +
        (t'.compile (pc + (c.compile 0 pc).length + 1)).length + 1)).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hb) (Stmt.compile_ne_nil _ _)
    | some y =>
      rw [hb] at h
      have := ihe _ (hb.trans h)
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  | seq s₁ s₂ ih₁ ih₂ =>
    simp only [Stmt.compile] at h ⊢
    rw [List.getLast?_append] at h
    cases hb : (s₂.compile (pc + (s₁.compile pc).length)).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hb) (Stmt.compile_ne_nil _ _)
    | some y =>
      rw [hb] at h
      have := ih₂ _ (hb.trans h)
      simp only [List.length_append]
      omega

theorem Stmt.compile_last_nop' (s : Stmt) (pc : ℕ) (l : List (Instr String ℕ)) (t : ℕ)
    (h : s.compile pc = l ++ [.nop t]) : t < pc + (s.compile pc).length :=
  Stmt.compile_last_nop s pc t (by rw [h]; simp)

/-- `if c then b end` and `if c' then t else e end` never compile to
overlapping code. -/
theorem ifThen_ne_ifElse {c c' : FExpr} {b t e : Stmt} (hc : c.Supported) (hc' : c'.Supported)
    {pc : ℕ} {r r' : List (Instr String ℕ)} :
    (Stmt.ifThen c b).compile pc ++ r ≠ (Stmt.ifElse c' t e).compile pc ++ r' := by
  intro h
  simp only [Stmt.compile, List.append_assoc, List.cons_append, List.nil_append] at h
  obtain ⟨rfl, h2⟩ := FExpr.compile_prefix hc hc' h
  obtain ⟨hI, hrest⟩ := List.cons.inj h2
  obtain ⟨-, -, -, hT, -⟩ := Instr.cmp.inj hI
  have h3 := hrest.trans (List.append_assoc _ [_] _).symm
  obtain ⟨hcb, -⟩ := List.append_inj h3
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hl := Stmt.compile_last_nop' b _ _ _ hcb
  omega

/-- Forms of non-sequence code in the injectivity proof. -/
theorem Stmt.q_of_np {s : Stmt} {pc : ℕ}
    (np : ∀ s' : Stmt, s'.Supported → s'.Canonical → ¬ s'.IsSeq → ∀ r r',
      s.compile pc ++ r = s'.compile pc ++ r' → s = s' ∧ r = r')
    (s' : Stmt) (hs' : s'.Supported) (hc' : s'.Canonical) (h : s.compile pc = s'.compile pc) :
    s = s' := by
  cases s'
  case seq a b =>
    rw [Stmt.canonical_seq] at hc'
    simp only [Stmt.Supported] at hs'
    have h' : s.compile pc ++ [] = a.compile pc ++ b.compile (pc + (a.compile pc).length) := by
      rw [List.append_nil]; exact h
    obtain ⟨-, hnil⟩ := np a hs'.1 hc'.2.1 hc'.1 _ _ h'
    exact absurd hnil.symm (Stmt.compile_ne_nil _ _)
  all_goals exact (np _ hs' hc' (by simp [Stmt.IsSeq]) [] []
    (by rw [List.append_nil, List.append_nil]; exact h)).1

theorem Stmt.compile_inj_aux (s : Stmt) : s.Supported → s.Canonical → ∀ pc : ℕ,
    (∀ s' : Stmt, s'.Supported → s'.Canonical → s.compile pc = s'.compile pc → s = s') ∧
    (¬ s.IsSeq → ∀ s' : Stmt, s'.Supported → s'.Canonical → ¬ s'.IsSeq → ∀ r r',
      s.compile pc ++ r = s'.compile pc ++ r' → s = s' ∧ r = r') := by
  induction s with
  | assign x e =>
    intro hs _ pc
    simp only [Stmt.Supported] at hs
    have np : ∀ s' : Stmt, s'.Supported → s'.Canonical → ¬ s'.IsSeq → ∀ r r',
        (Stmt.assign x e).compile pc ++ r = s'.compile pc ++ r' → Stmt.assign x e = s' ∧ r = r' := by
      intro s' hs' hc' hns' r r' h
      cases s' with
      | assign x' e' =>
        simp only [Stmt.Supported] at hs'
        simp only [Stmt.compile, List.append_assoc, List.cons_append, List.nil_append] at h
        obtain ⟨rfl, h2⟩ := FExpr.compile_prefix hs.2 hs'.2 h
        obtain ⟨hI, hr⟩ := List.cons.inj h2
        obtain ⟨-, rfl, -, -⟩ := Instr.alu2.inj hI
        exact ⟨rfl, hr⟩
      | forLoop x' lo' hi' b' =>
        simp only [Stmt.Supported] at hs'
        simp only [Stmt.compile, List.append_assoc, List.cons_append, List.nil_append] at h
        exact absurd h.symm (mov_cons_ne_expr hs'.1 e 0 pc)
      | ifThen c' b' =>
        simp only [Stmt.Supported] at hs'
        simp only [Stmt.compile, List.append_assoc, List.cons_append, List.nil_append] at h
        obtain ⟨rfl, h2⟩ := FExpr.compile_prefix hs.2 hs'.1 h
        obtain ⟨hI, -⟩ := List.cons.inj h2
        cases hI
      | ifElse c' t' e' =>
        simp only [Stmt.Supported] at hs'
        simp only [Stmt.compile, List.append_assoc, List.cons_append, List.nil_append] at h
        obtain ⟨rfl, h2⟩ := FExpr.compile_prefix hs.2 hs'.1 h
        obtain ⟨hI, -⟩ := List.cons.inj h2
        cases hI
      | seq => exact absurd trivial hns'
    exact ⟨Stmt.q_of_np np, fun _ => np⟩
  | forLoop x lo hi b ih =>
    intro hs hc pc
    simp only [Stmt.Supported] at hs
    simp only [Stmt.Canonical] at hc
    have np : ∀ s' : Stmt, s'.Supported → s'.Canonical → ¬ s'.IsSeq → ∀ r r',
        (Stmt.forLoop x lo hi b).compile pc ++ r = s'.compile pc ++ r' →
          Stmt.forLoop x lo hi b = s' ∧ r = r' := by
      intro s' hs' hc' hns' r r' h
      cases s' with
      | forLoop x' lo' hi' b' =>
        simp only [Stmt.Supported] at hs'
        simp only [Stmt.Canonical] at hc'
        simp only [Stmt.compile, List.append_assoc, List.cons_append, List.nil_append] at h
        obtain ⟨hM, h1⟩ := List.cons.inj h
        obtain ⟨hC, h2⟩ := List.cons.inj h1
        obtain ⟨-, rfl, hlo, -⟩ := Instr.alu2.inj hM
        obtain ⟨-, -, hhi, hT, -⟩ := Instr.cmp.inj hC
        obtain rfl := Operand.imm.inj hlo
        obtain rfl := Operand.imm.inj hhi
        obtain ⟨hcb, h3⟩ := List.append_inj h2 (by omega)
        obtain rfl := (ih hs.2.2 hc (pc + 2)).1 b' hs'.2.2 hc' hcb
        exact ⟨rfl, (List.cons.inj (List.cons.inj h3).2).2⟩
      | assign x' e' =>
        simp only [Stmt.Supported] at hs'
        simp only [Stmt.compile, List.append_assoc, List.cons_append, List.nil_append] at h
        exact absurd h (mov_cons_ne_expr hs.1 e' 0 pc)
      | ifThen c' b' =>
        simp only [Stmt.Supported] at hs'
        simp only [Stmt.compile, List.append_assoc, List.cons_append, List.nil_append] at h
        exact absurd h (mov_cons_ne_expr hs.1 c' 0 pc)
      | ifElse c' t' e' =>
        simp only [Stmt.Supported] at hs'
        simp only [Stmt.compile, List.append_assoc, List.cons_append, List.nil_append] at h
        exact absurd h (mov_cons_ne_expr hs.1 c' 0 pc)
      | seq => exact absurd trivial hns'
    exact ⟨Stmt.q_of_np np, fun _ => np⟩
  | ifThen c b ih =>
    intro hs hc pc
    simp only [Stmt.Supported] at hs
    simp only [Stmt.Canonical] at hc
    have np : ∀ s' : Stmt, s'.Supported → s'.Canonical → ¬ s'.IsSeq → ∀ r r',
        (Stmt.ifThen c b).compile pc ++ r = s'.compile pc ++ r' →
          Stmt.ifThen c b = s' ∧ r = r' := by
      intro s' hs' hc' hns' r r' h
      cases s' with
      | ifThen c' b' =>
        simp only [Stmt.Supported] at hs'
        simp only [Stmt.Canonical] at hc'
        simp only [Stmt.compile, List.append_assoc, List.cons_append, List.nil_append] at h
        obtain ⟨rfl, h2⟩ := FExpr.compile_prefix hs.1 hs'.1 h
        obtain ⟨hI, h3⟩ := List.cons.inj h2
        obtain ⟨-, -, -, hT, -⟩ := Instr.cmp.inj hI
        obtain ⟨hcb, hr⟩ := List.append_inj h3 (by omega)
        obtain rfl := (ih hs.2 hc _).1 b' hs'.2 hc' hcb
        exact ⟨rfl, hr⟩
      | ifElse c' t' e' =>
        simp only [Stmt.Supported] at hs'
        exact absurd h (ifThen_ne_ifElse hs.1 hs'.1)
      | assign x' e' =>
        simp only [Stmt.Supported] at hs'
        simp only [Stmt.compile, List.append_assoc, List.cons_append, List.nil_append] at h
        obtain ⟨rfl, h2⟩ := FExpr.compile_prefix hs.1 hs'.2 h
        obtain ⟨hI, -⟩ := List.cons.inj h2
        cases hI
      | forLoop x' lo' hi' b' =>
        simp only [Stmt.Supported] at hs'
        simp only [Stmt.compile, List.append_assoc, List.cons_append, List.nil_append] at h
        exact absurd h.symm (mov_cons_ne_expr hs'.1 c 0 pc)
      | seq => exact absurd trivial hns'
    exact ⟨Stmt.q_of_np np, fun _ => np⟩
  | ifElse c t e iht ihe =>
    intro hs hc pc
    simp only [Stmt.Supported] at hs
    simp only [Stmt.Canonical] at hc
    have np : ∀ s' : Stmt, s'.Supported → s'.Canonical → ¬ s'.IsSeq → ∀ r r',
        (Stmt.ifElse c t e).compile pc ++ r = s'.compile pc ++ r' →
          Stmt.ifElse c t e = s' ∧ r = r' := by
      intro s' hs' hc' hns' r r' h
      cases s' with
      | ifElse c' t' e' =>
        simp only [Stmt.Supported] at hs'
        simp only [Stmt.Canonical] at hc'
        simp only [Stmt.compile, List.append_assoc, List.cons_append, List.nil_append] at h
        obtain ⟨rfl, h2⟩ := FExpr.compile_prefix hs.1 hs'.1 h
        obtain ⟨hI, h3⟩ := List.cons.inj h2
        obtain ⟨-, -, -, hT, -⟩ := Instr.cmp.inj hI
        obtain ⟨hct, h4⟩ := List.append_inj h3 (by omega)
        obtain rfl := (iht hs.2.1 hc.1 _).1 t' hs'.2.1 hc'.1 hct
        obtain ⟨hN, h5⟩ := List.cons.inj h4
        have hN' := Instr.nop.inj hN
        obtain ⟨hce, hr⟩ := List.append_inj h5 (by omega)
        obtain rfl := (ihe hs.2.2 hc.2 _).1 e' hs'.2.2 hc'.2 hce
        exact ⟨rfl, hr⟩
      | ifThen c' b' =>
        simp only [Stmt.Supported] at hs'
        exact absurd h.symm (ifThen_ne_ifElse hs'.1 hs.1)
      | assign x' e' =>
        simp only [Stmt.Supported] at hs'
        simp only [Stmt.compile, List.append_assoc, List.cons_append, List.nil_append] at h
        obtain ⟨rfl, h2⟩ := FExpr.compile_prefix hs.1 hs'.2 h
        obtain ⟨hI, -⟩ := List.cons.inj h2
        cases hI
      | forLoop x' lo' hi' b' =>
        simp only [Stmt.Supported] at hs'
        simp only [Stmt.compile, List.append_assoc, List.cons_append, List.nil_append] at h
        exact absurd h.symm (mov_cons_ne_expr hs'.1 c 0 pc)
      | seq => exact absurd trivial hns'
    exact ⟨Stmt.q_of_np np, fun _ => np⟩
  | seq s₁ s₂ ih₁ ih₂ =>
    intro hs hc pc
    simp only [Stmt.Supported] at hs
    rw [Stmt.canonical_seq] at hc
    refine ⟨fun s' hs' hc' h => ?_, fun hns => absurd trivial hns⟩
    have h0 : s₁.compile pc ++ s₂.compile (pc + (s₁.compile pc).length) = s'.compile pc := h
    cases s'
    case seq a b =>
      rw [Stmt.canonical_seq] at hc'
      simp only [Stmt.Supported] at hs'
      have h' : s₁.compile pc ++ s₂.compile (pc + (s₁.compile pc).length) =
          a.compile pc ++ b.compile (pc + (a.compile pc).length) := h
      obtain ⟨rfl, h2⟩ := (ih₁ hs.1 hc.2.1 pc).2 hc.1 a hs'.1 hc'.2.1 hc'.1 _ _ h'
      rw [(ih₂ hs.2 hc.2.2 _).1 b hs'.2 hc'.2.2 h2]
    all_goals
      have h' : s₁.compile pc ++ s₂.compile (pc + (s₁.compile pc).length) = _ ++ [] :=
        h0.trans (List.append_nil _).symm
      obtain ⟨-, hnil⟩ := (ih₁ hs.1 hc.2.1 pc).2 hc.1 _ hs' hc' (by simp [Stmt.IsSeq]) _ _ h'
      exact absurd hnil (Stmt.compile_ne_nil _ _)

/-- Compilation is injective on supported canonical programs, so compiled code
has a unique decompilation. (Without canonical form it is not: `seq` is
compiled associatively.) -/
theorem compile_injective {s s' : Stmt} (hs : s.Supported) (hs' : s'.Supported)
    (hc : s.Canonical) (hc' : s'.Canonical) (h : s.compile 0 = s'.compile 0) : s = s' :=
  (Stmt.compile_inj_aux s hs hc 0).1 s' hs' hc' h

end Silmaril.Courses.Cambridge.OptimisingCompilers.Decompilation
