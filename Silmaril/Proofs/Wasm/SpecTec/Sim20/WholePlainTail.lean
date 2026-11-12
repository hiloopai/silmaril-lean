module

public import Silmaril.Wasm.V2.Execution.Step

/-!
# The 2.0 plain-tail invariant: plain code after V2's redex

The 2.0 script quantifies the code after a `br`, `return` or `trap` redex as `instr*`, while V2
allows any administrative code there (`Whole.PureRest20`'s three tail cases). V2 reduces the
leftmost redex, so in a run from plain code everything after it is still plain, with one
exception: `table.fill-succ`, `table.init-succ` and `memory.fill-succ` put a value (for the table
rules a reference, `REF.FUNC_ADDR`, which is an `admininstr` but not an `instr`) *after* their
`table.set` or `i32.store8`. That operator is the next redex and is in range by the premise of the
expanding rule, so it never traps, and the value reaches the front before any `br`, `return` or
`trap` can see it.

`Plain20 s f code` says exactly this, recursively in label and frame bodies (frame bodies read in
the inner frame):

* the code is `val*`, or `val* x instr*` with `x` a non-value source instruction, `TRAP`,
  `CALL_ADDR`, or a label or frame with a `Plain20` body;
* or it has a *pending in-range operator*, `val* (CONST I32 i) val y val'* instr*` with `y` a
  `table.set x` or `i32.store8` (`PendOp`) that is in range at `i` (`PendOk`: `SetOk`, `MemOk`).

Proved here:

* `Plain20.split`: at its first non-value, `Plain20` code has a plain suffix and well-formed
  bodies, or a pending in-range operator;
* `step_pendHead`: every V2 step from `val* y rest`, `y` a pending operator, is that operator;
* **`plain20_step`**, **`plain20_steps`**: every V2 step and run preserves `Plain20`;
  `plain20_invoke`, `plain20_expression`: invocation code and plain code satisfy it;
* `Tail20` (`Plain20`, or a pending-operator head) passes to the inner code of each context
  (`tail20_ctx`, `tail20_label`, `tail20_frame`), and at a first non-value that is not a pending
  operator the code after it is plain (`Tail20.plain_after`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-! ## First non-values -/

/-- The `i32` value `i`. -/
abbrev i32V (i : BitVec 32) : Val := .num ⟨.int .i32, i⟩

@[simp] theorem toAdmin_i32V (i : BitVec 32) : (i32V i).toAdmin = constI32 i := rfl

/-- Two splits of the same code at a non-value agree. -/
theorem vals_cons_inj20 {a b : List Val} {x y : Admin} {L M : List Admin}
    (hx : x.isVal = false) (hy : y.isVal = false) (h : vals a ++ x :: L = vals b ++ y :: M) :
    a = b ∧ x = y ∧ L = M := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simpa using h
    | cons v b =>
      simp only [vals_nil, List.nil_append, vals_cons, List.cons_append, List.cons.injEq] at h
      rw [h.1, Admin.isVal_toAdmin] at hx
      exact absurd hx (by decide)
  | cons u a ih =>
    cases b with
    | nil =>
      simp only [vals_cons, List.cons_append, vals_nil, List.nil_append, List.cons.injEq] at h
      rw [← h.1, Admin.isVal_toAdmin] at hy
      exact absurd hy (by decide)
    | cons v b =>
      simp only [vals_cons, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := ih h.2
      exact ⟨by rw [Val.toAdmin_injective h.1], rfl, rfl⟩

/-- Code that is not all values splits at its first non-value. -/
theorem exists_split20 {l : List Admin} (h : l.all Admin.isVal = false) :
    ∃ p y q, l = vals p ++ y :: q ∧ y.isVal = false := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    cases hx : x.isVal with
    | false => exact ⟨[], x, l, rfl, hx⟩
    | true =>
      rw [List.all_cons, hx, Bool.true_and] at h
      obtain ⟨p, y, q, rfl, hy⟩ := ih h
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (show x.val?.isSome from hx)
      exact ⟨v :: p, y, q, by rw [vals_cons, ← Admin.toAdmin_of_val? hv]; rfl, hy⟩

/-- A value in `val*` is a value. -/
theorem not_mem_vals_of {vs : List Val} {y : Admin} (hy : y.isVal = false) : y ∉ vals vs :=
  fun hm => by rw [isVal_of_mem_vals hm] at hy; exact absurd hy (by decide)

/-- The first non-value of `val* y M`, if `y` is not a value. -/
theorem find_vals_cons {a : List Val} {y : Admin} {M : List Admin} (hy : y.isVal = false) :
    (vals a ++ y :: M).find? (fun z => !z.isVal) = some y := by
  induction a with
  | nil => simp [hy]
  | cons v a ih => simpa using ih

@[simp] theorem find_vals {a : List Val} : (vals a).find? (fun z => !z.isVal) = none := by
  induction a with
  | nil => rfl
  | cons v a ih => simpa using ih

/-- The first non-value of `val* rest`. -/
theorem find_vals_append {a : List Val} {M : List Admin} :
    (vals a ++ M).find? (fun z => !z.isVal) = M.find? (fun z => !z.isVal) := by
  induction a with
  | nil => rfl
  | cons v a ih => simp [ih]

/-! ## Values, by head -/

theorem isVal_plain (i : V2.Instr) : (Admin.plain i).isVal = (Admin.plain i).val?.isSome := rfl
@[simp] theorem isVal_callAddr (a : FuncAddr) : (Admin.callAddr a).isVal = false := rfl
@[simp] theorem isVal_label (n : Nat) (cont : List V2.Instr) (body : List Admin) :
    (Admin.label n cont body).isVal = false := rfl
@[simp] theorem isVal_frame (n : Nat) (fi : Frame) (body : List Admin) :
    (Admin.frame n fi body).isVal = false := rfl
@[simp] theorem isVal_trap : (Admin.trap).isVal = false := rfl
@[simp] theorem isVal_refFuncAddr (a : FuncAddr) : (Admin.refFuncAddr a).isVal = true := rfl
@[simp] theorem isVal_refHostAddr (a : HostAddr) : (Admin.refHostAddr a).isVal = true := rfl

@[simp] theorem find_toAdmin_cons (v : Val) (l : List Admin) :
    (v.toAdmin :: l).find? (fun z => !z.isVal) = l.find? (fun z => !z.isVal) := by
  simp

/-- A source instruction. -/
def isPlainA : Admin → Bool
  | .plain _ => true
  | _ => false

/-- A first non-value that `Plain20` accepts without a body: a source instruction, `TRAP`,
`CALL_ADDR`. -/
def isFlatHead : Admin → Bool
  | .plain _ => true
  | .trap => true
  | .callAddr _ => true
  | _ => false

/-- **Flat code**: values, then at most a flat head followed by source instructions. -/
def flatOk : List Admin → Bool
  | [] => true
  | x :: l => if x.isVal then flatOk l else isFlatHead x && l.all isPlainA

@[simp] theorem flatOk_nil : flatOk [] = true := rfl
@[simp] theorem flatOk_toAdmin (v : Val) (l : List Admin) : flatOk (v.toAdmin :: l) = flatOk l := by
  simp [flatOk]
@[simp] theorem flatOk_vals_append (vs : List Val) (l : List Admin) :
    flatOk (vals vs ++ l) = flatOk l := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simpa using ih
@[simp] theorem all_isPlainA_expression (is : List V2.Instr) : (expression is).all isPlainA = true := by
  simp [expression, isPlainA]

theorem eq_expression_of_all {l : List Admin} (h : l.all isPlainA = true) :
    ∃ is, l = expression is := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons x l ih =>
    rw [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨is, rfl⟩ := ih h.2
    cases x with
    | plain i => exact ⟨i :: is, rfl⟩
    | _ => simp [isPlainA] at h

/-! ## The invariant -/

/-- `table.set` at index `i` of table `x` is in range at `(s, f)`. -/
def SetOk (s : Store H) (f : Frame) (x : TableIdx) (i : BitVec 32) : Prop :=
  ∀ a ti, f.module.tableAddr? x = some a → s.tableInst? a = some ti → i.toNat < ti.refs.length

/-- `i32.store8` at address `i` (offset 0) is in range of memory 0 at `(s, f)`. -/
def MemOk (s : Store H) (f : Frame) (i : BitVec 32) : Prop :=
  ∀ a mi, f.module.memAddr? memIdx0 = some a → s.memInst? a = some mi →
    effAddr i.toNat memarg0 + 1 ≤ mi.bytes.size

/-- The operators that the bulk rules (`table.fill`, `table.init`, `memory.fill`) leave pending
with a value after them: `table.set x` and `i32.store8`. -/
def PendOp (y : Admin) : Prop := (∃ x, y = .plain (.tableSet x)) ∨ y = store8

/-- The pending operator `y` at index `i` is in range. -/
def PendOk (s : Store H) (f : Frame) (y : Admin) (i : BitVec 32) : Prop :=
  (∀ x, y = .plain (.tableSet x) → SetOk s f x i) ∧ (y = store8 → MemOk s f i)

theorem PendOp.isVal {y : Admin} (h : PendOp y) : y.isVal = false := by
  rcases h with ⟨x, rfl⟩ | rfl <;> rfl

/-- **The plain-tail invariant** (see the module docstring). -/
inductive Plain20 : Store H → Frame → List Admin → Prop where
  | allVals {s : Store H} {f : Frame} (vs : List Val) : Plain20 s f (vals vs)
  | plain {s : Store H} {f : Frame} (vs : List Val) (i : V2.Instr) (is : List V2.Instr)
      (hi : (Admin.plain i).isVal = false) : Plain20 s f (vals vs ++ .plain i :: expression is)
  | trap {s : Store H} {f : Frame} (vs : List Val) (is : List V2.Instr) :
      Plain20 s f (vals vs ++ .trap :: expression is)
  | callAddr {s : Store H} {f : Frame} (vs : List Val) (a : FuncAddr) (is : List V2.Instr) :
      Plain20 s f (vals vs ++ .callAddr a :: expression is)
  | label {s : Store H} {f : Frame} (vs : List Val) (n : Nat) (cont : List V2.Instr)
      (body : List Admin) (is : List V2.Instr) (hb : Plain20 s f body) :
      Plain20 s f (vals vs ++ .label n cont body :: expression is)
  | frame {s : Store H} {f : Frame} (vs : List Val) (n : Nat) (fi : Frame) (body : List Admin)
      (is : List V2.Instr) (hb : Plain20 s fi body) :
      Plain20 s f (vals vs ++ .frame n fi body :: expression is)
  | pend {s : Store H} {f : Frame} (vs : List Val) (i : BitVec 32) (v : Val) (y : Admin)
      (ws : List Val) (is : List V2.Instr) (hy : PendOp y) (hok : PendOk s f y i) :
      Plain20 s f (vals (vs ++ [i32V i, v]) ++ y :: (vals ws ++ expression is))

/-- The bodies of a label or frame head are `Plain20` (a frame's in its own frame). -/
def HeadOk (s : Store H) (f : Frame) (y : Admin) : Prop :=
  (∀ n cont body, y = .label n cont body → Plain20 s f body) ∧
    ∀ n fi body, y = .frame n fi body → Plain20 s fi body

theorem headOk_of {s : Store H} {f : Frame} {y : Admin} (hl : ∀ n cont body, y ≠ .label n cont body)
    (hf : ∀ n fi body, y ≠ .frame n fi body) : HeadOk s f y :=
  ⟨fun n cont body h => absurd h (hl n cont body), fun n fi body h => absurd h (hf n fi body)⟩

/-- Values followed by plain instructions are `Plain20`. -/
theorem plain20_vals_expr {s : Store H} {f : Frame} (vs : List Val) (is : List V2.Instr) :
    Plain20 s f (vals vs ++ expression is) := by
  induction is generalizing vs with
  | nil => simpa [expression] using Plain20.allVals vs
  | cons i is ih =>
    cases hi : (Admin.plain i).isVal with
    | false => exact .plain vs i is hi
    | true =>
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (show (Admin.plain i).val?.isSome from hi)
      have e : vals vs ++ expression (i :: is) = vals (vs ++ [v]) ++ expression is := by
        simp [expression, Admin.toAdmin_of_val? hv]
      exact e ▸ ih _

/-- Plain code is `Plain20`. -/
theorem plain20_expression {s : Store H} {f : Frame} (is : List V2.Instr) :
    Plain20 s f (expression is) := by simpa using plain20_vals_expr (s := s) (f := f) [] is

/-- **Building `Plain20`** from a first non-value with well-formed bodies and a plain suffix. -/
theorem plain20_build {s : Store H} {f : Frame} (vs : List Val) {y : Admin} (hy : y.isVal = false)
    (hh : HeadOk s f y) (is : List V2.Instr) : Plain20 s f (vals vs ++ y :: expression is) := by
  cases y with
  | plain i => exact .plain vs i is hy
  | refFuncAddr a => simp [Admin.isVal, Admin.val?] at hy
  | refHostAddr a => simp [Admin.isVal, Admin.val?] at hy
  | callAddr a => exact .callAddr vs a is
  | label n cont body => exact .label vs n cont body is (hh.1 n cont body rfl)
  | frame n fi body => exact .frame vs n fi body is (hh.2 n fi body rfl)
  | trap => exact .trap vs is

/-- `Plain20` code with values in front and plain instructions behind. -/
theorem plain20_wrap {s : Store H} {f : Frame} {l : List Admin} (h : Plain20 s f l) (vs : List Val)
    (is : List V2.Instr) : Plain20 s f (vals vs ++ l ++ expression is) := by
  cases h with
  | allVals ws => simpa using plain20_vals_expr (s := s) (f := f) (vs ++ ws) is
  | plain ws i js hi =>
    simpa [expression] using Plain20.plain (s := s) (f := f) (vs ++ ws) i (js ++ is) hi
  | trap ws js => simpa [expression] using Plain20.trap (s := s) (f := f) (vs ++ ws) (js ++ is)
  | callAddr ws a js =>
    simpa [expression] using Plain20.callAddr (s := s) (f := f) (vs ++ ws) a (js ++ is)
  | label ws n cont body js hb =>
    simpa [expression] using Plain20.label (vs ++ ws) n cont body (js ++ is) hb
  | frame ws n fi body js hb =>
    simpa [expression] using Plain20.frame (f := f) (vs ++ ws) n fi body (js ++ is) hb
  | pend ws i v y us js hy hok =>
    simpa [expression] using Plain20.pend (vs ++ ws) i v y us (js ++ is) hy hok

/-- **Flat code is `Plain20`.** -/
theorem plain20_of_flatOk {s : Store H} {f : Frame} {l : List Admin} (h : flatOk l = true) :
    Plain20 s f l := by
  induction l with
  | nil => exact .allVals []
  | cons x l ih =>
    cases hx : x.isVal with
    | true =>
      simp only [flatOk, hx, ↓reduceIte] at h
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (show x.val?.isSome from hx)
      rw [← Admin.toAdmin_of_val? hv]
      simpa [expression] using plain20_wrap (ih h) [v] []
    | false =>
      simp only [flatOk, hx, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at h
      obtain ⟨is, rfl⟩ := eq_expression_of_all h.2
      simpa using plain20_build [] hx (headOk_of (s := s) (f := f)
        (fun n c b he => by subst he; simp [isFlatHead] at h)
        (fun n fi b he => by subst he; simp [isFlatHead] at h)) is

/-! ## Reading the invariant -/

/-- A pending in-range operator at the first non-value `y`. -/
def PendHead (s : Store H) (f : Frame) (a : List Val) (y : Admin) (M : List Admin) : Prop :=
  ∃ us i v ws is, a = us ++ [i32V i, v] ∧ PendOp y ∧ M = vals ws ++ expression is ∧
    PendOk s f y i

/-- A label head with a `Plain20` body. -/
theorem headOk_label {s : Store H} {f : Frame} {n : Nat} {cont : List V2.Instr} {body : List Admin}
    (hb : Plain20 s f body) : HeadOk s f (.label n cont body) :=
  ⟨fun _ _ _ h => (by cases h; exact hb), fun _ _ _ h => (by cases h)⟩

/-- A frame head with a `Plain20` body. -/
theorem headOk_frame {s : Store H} {f fi : Frame} {n : Nat} {body : List Admin}
    (hb : Plain20 s fi body) : HeadOk s f (.frame n fi body) :=
  ⟨fun _ _ _ h => (by cases h), fun _ _ _ h => (by cases h; exact hb)⟩

/-- A head without a body. -/
theorem headOk_flat {s : Store H} {f : Frame} {y : Admin} (hy : isFlatHead y = true) :
    HeadOk s f y :=
  headOk_of (fun _ _ _ h => by subst h; simp [isFlatHead] at hy)
    (fun _ _ _ h => by subst h; simp [isFlatHead] at hy)

/-- A split that meets a constructor of `Plain20` at its first non-value. -/
theorem split_hit {s : Store H} {f : Frame} {a vs : List Val} {y z : Admin} {M : List Admin}
    {is : List V2.Instr} (hy : y.isVal = false) (hz : z.isVal = false)
    (hc : vals a ++ y :: M = vals vs ++ z :: expression is) (hh : HeadOk s f z) :
    ((∃ is, M = expression is) ∧ HeadOk s f y) ∨ PendHead s f a y M := by
  obtain ⟨-, rfl, rfl⟩ := vals_cons_inj20 hy hz hc
  exact .inl ⟨⟨is, rfl⟩, hh⟩

/-- A split that meets a pending operator. -/
theorem split_pend {s : Store H} {f : Frame} {a vs ws : List Val} {i : BitVec 32} {v : Val}
    {y z : Admin} {M : List Admin} {is : List V2.Instr} (hy : y.isVal = false) (hz : PendOp z)
    (hok : PendOk s f z i)
    (hc : vals a ++ y :: M = vals (vs ++ [i32V i, v]) ++ z :: (vals ws ++ expression is)) :
    ((∃ is, M = expression is) ∧ HeadOk s f y) ∨ PendHead s f a y M := by
  obtain ⟨rfl, rfl, rfl⟩ := vals_cons_inj20 hy hz.isVal hc
  exact .inr ⟨vs, i, v, ws, is, rfl, hz, rfl, hok⟩

/-- **`Plain20`, read at its first non-value**: a plain suffix and well-formed bodies, or a
pending in-range operator. -/
theorem Plain20.split {s : Store H} {f : Frame} {a : List Val} {y : Admin} {M : List Admin}
    (h : Plain20 s f (vals a ++ y :: M)) (hy : y.isVal = false) :
    ((∃ is, M = expression is) ∧ HeadOk s f y) ∨ PendHead s f a y M := by
  generalize hc : vals a ++ y :: M = code at h
  cases h with
  | allVals vs =>
    exact absurd (hc ▸ List.mem_append_right _ List.mem_cons_self) (not_mem_vals_of hy)
  | plain vs i is hi => exact split_hit hy hi hc (headOk_flat rfl)
  | trap vs is => exact split_hit hy rfl hc (headOk_flat rfl)
  | callAddr vs b is => exact split_hit hy rfl hc (headOk_flat rfl)
  | label vs n cont body is hb => exact split_hit hy rfl hc (headOk_label hb)
  | frame vs n fi body is hb => exact split_hit hy rfl hc (headOk_frame hb)
  | pend vs i v y' ws is hy' hok => exact split_pend hy hy' hok hc

theorem not_pendOp_label {n : Nat} {cont : List V2.Instr} {body : List Admin} :
    ¬ PendOp (.label n cont body) := by
  rintro (⟨_, h⟩ | h) <;> cases h

theorem not_pendOp_frame {n : Nat} {fi : Frame} {body : List Admin} :
    ¬ PendOp (.frame n fi body) := by
  rintro (⟨_, h⟩ | h) <;> cases h

/-- A one-element label code has a `Plain20` body. -/
theorem Plain20.label_body {s : Store H} {f : Frame} {n : Nat} {cont : List V2.Instr}
    {body : List Admin} (h : Plain20 s f [.label n cont body]) : Plain20 s f body := by
  rcases (show [(.label n cont body : Admin)] = vals [] ++ Admin.label n cont body :: [] from rfl) ▸ h
    |>.split rfl with ⟨-, hh⟩ | ⟨_, _, _, _, _, -, hp, -, -⟩
  · exact hh.1 n cont body rfl
  · exact absurd hp not_pendOp_label

/-- A one-element frame code has a `Plain20` body, in the inner frame. -/
theorem Plain20.frame_body {s : Store H} {f fi : Frame} {n : Nat} {body : List Admin}
    (h : Plain20 s f [.frame n fi body]) : Plain20 s fi body := by
  rcases (show [(.frame n fi body : Admin)] = vals [] ++ Admin.frame n fi body :: [] from rfl) ▸ h
    |>.split rfl with ⟨-, hh⟩ | ⟨_, _, _, _, _, -, hp, -, -⟩
  · exact hh.2 n fi body rfl
  · exact absurd hp not_pendOp_frame

/-! ## Steps from a pending operator -/

/-- The first non-value of code starting with a non-value. -/
theorem find_cons_nonval {y : Admin} (l : List Admin) (hy : y.isVal = false) :
    (y :: l).find? (fun z => !z.isVal) = some y := by simp [hy]

/-- No `Step_pure` rule has a pending operator as its first non-value. -/
theorem pure_find_not_pend {P : Profile} {is is' : List Admin} (h : PureStep P is is') {y : Admin}
    (hy : PendOp y) : is.find? (fun z => !z.isVal) ≠ some y := by
  rcases hy with ⟨x, rfl⟩ | rfl <;> cases h <;>
    simp [isVal_plain, Admin.val?, store8, memarg0]

/-- No `Step_read` rule has a pending operator as its first non-value. -/
theorem read_find_not_pend {s : Store H} {f : Frame} {is is' : List Admin}
    (h : ReadStep s f is is') {y : Admin} (hy : PendOp y) :
    is.find? (fun z => !z.isVal) ≠ some y := by
  rcases hy with ⟨x, rfl⟩ | rfl <;> cases h <;>
    simp [isVal_plain, Admin.val?, store8, memarg0]

/-- What a step from a pending operator does. -/
def PendResult (s : Store H) (f : Frame) (a : List Val) (y : Admin) (L : List Admin)
    (c' : Config H) : Prop :=
  ∃ a' i w, a = a' ++ [i32V i, w] ∧ c'.frame = f ∧
    (c'.code = vals a' ++ L ∨ (c'.code = vals a' ++ .trap :: L ∧ ¬ PendOk s f y i))

theorem pendResult_append {s : Store H} {f : Frame} {vs p : List Val} {y : Admin}
    {q rest : List Admin} {c' : Config H} (h : PendResult s f p y q c') :
    PendResult s f (vs ++ p) y (q ++ rest) ⟨c'.store, c'.frame, vals vs ++ c'.code ++ rest⟩ := by
  obtain ⟨a', i, w, rfl, hf, hc⟩ := h
  refine ⟨vs ++ a', i, w, by simp, hf, ?_⟩
  rcases hc with hc | ⟨hc, hn⟩
  · exact .inl (by simp [hc])
  · exact .inr ⟨by simp [hc], hn⟩

/-- The first non-value of a code that steps, as an equation. -/
theorem find_eq_of_eq {a : List Val} {y : Admin} {L : List Admin} {code : List Admin}
    (hy : y.isVal = false) (h : code = vals a ++ y :: L) :
    code.find? (fun z => !z.isVal) = some y := h ▸ find_vals_cons hy

/-- A pending operator is not the first non-value of code whose first non-value is `z`. -/
theorem not_pend_of_find {code : List Admin} {a : List Val} {y z : Admin} {L : List Admin}
    (hy : PendOp y) (hc : code = vals a ++ y :: L) (hz : code.find? (fun z => !z.isVal) = some z)
    (hne : ¬ PendOp z) : False := by
  rw [find_eq_of_eq hy.isVal hc] at hz
  cases hz
  exact hne hy

/-- A code with no pending operator as its first non-value does not start one. -/
theorem pend_absurd {code : List Admin} {a : List Val} {y : Admin} {L : List Admin}
    (hy : PendOp y) (hc : code = vals a ++ y :: L)
    (hf : ∀ y, PendOp y → code.find? (fun z => !z.isVal) ≠ some y) : False :=
  hf y hy (find_eq_of_eq hy.isVal hc)

/-- `table.set-trap` at a pending operator. -/
theorem pendResult_tableSetTrap {s : Store H} {f : Frame} {x : TableIdx} {i : BitVec 32} {r : Ref}
    {ta : TableAddr} {ti : TableInst} (ha : f.module.tableAddr? x = some ta)
    (ht : s.tableInst? ta = some ti) (hlen : ti.refs.length ≤ i.toNat) {a : List Val} {y : Admin}
    {L : List Admin} (hy : PendOp y)
    (hc : [constI32 i, aref r, Admin.plain (.tableSet x)] = vals a ++ y :: L) :
    PendResult s f a y L ⟨s, f, [.trap]⟩ := by
  have e : [constI32 i, aref r, Admin.plain (.tableSet x)] =
    vals [i32V i, .ref r] ++ .plain (.tableSet x) :: [] := rfl
  obtain ⟨rfl, rfl, rfl⟩ := vals_cons_inj20 rfl hy.isVal (e ▸ hc)
  exact ⟨[], i, .ref r, rfl, rfl, .inr ⟨rfl, fun hok => absurd (hok.1 x rfl _ _ ha ht)
    (by omega)⟩⟩

/-- `table.set-val` at a pending operator. -/
theorem pendResult_tableSetVal {s s' : Store H} {f : Frame} {x : TableIdx} {i : BitVec 32}
    {r : Ref} {a : List Val} {y : Admin} {L : List Admin} (hy : PendOp y)
    (hc : [constI32 i, aref r, Admin.plain (.tableSet x)] = vals a ++ y :: L) :
    PendResult s f a y L ⟨s', f, []⟩ := by
  have e : [constI32 i, aref r, Admin.plain (.tableSet x)] =
    vals [i32V i, .ref r] ++ .plain (.tableSet x) :: [] := rfl
  obtain ⟨rfl, rfl, rfl⟩ := vals_cons_inj20 rfl hy.isVal (e ▸ hc)
  exact ⟨[], i, .ref r, rfl, rfl, .inl rfl⟩

/-- A pending `i32.store8` read back from a packed store. -/
theorem store8_of_pend {t : IntType} {sz : PackSize} {ao : V2.MemArg} (hy : PendOp (.plain
    (.intStore t (some sz) ao))) : t = .i32 ∧ sz = .i8 ∧ ao = memarg0 := by
  rcases hy with ⟨x, hx⟩ | hx
  · cases hx
  · simpa only [store8, Admin.plain.injEq, V2.Instr.intStore.injEq, Option.some.injEq] using hx

/-- `store-pack-trap` at a pending operator. -/
theorem pendResult_storePackTrap {s : Store H} {f : Frame} {t : IntType} {sz : PackSize}
    {ao : V2.MemArg} {i : BitVec 32} {k : BitVec t.width} {ma : MemAddr} {mi : MemInst}
    (ha : f.module.memAddr? memIdx0 = some ma) (hm : s.memInst? ma = some mi)
    (hlen : mi.bytes.size < effAddr i.toNat ao + sz.width / 8) {a : List Val} {y : Admin}
    {L : List Admin} (hy : PendOp y)
    (hc : [constI32 i, Admin.plain (.intConst t k), Admin.plain (.intStore t (some sz) ao)] =
      vals a ++ y :: L) :
    PendResult s f a y L ⟨s, f, [.trap]⟩ := by
  have e : [constI32 i, Admin.plain (.intConst t k), Admin.plain (.intStore t (some sz) ao)] =
    vals [i32V i, .num ⟨.int t, k⟩] ++ .plain (.intStore t (some sz) ao) :: [] := rfl
  obtain ⟨rfl, rfl, rfl⟩ := vals_cons_inj20 rfl hy.isVal (e ▸ hc)
  obtain ⟨rfl, rfl, rfl⟩ := store8_of_pend hy
  refine ⟨[], i, _, rfl, rfl, .inr ⟨rfl, fun hok => ?_⟩⟩
  have h1 : effAddr i.toNat memarg0 + 1 ≤ mi.bytes.size := hok.2 rfl _ _ ha hm
  have h2 : mi.bytes.size < effAddr i.toNat memarg0 + 1 := by simpa [PackSize.width] using hlen
  omega

/-- `store-pack-val` at a pending operator. -/
theorem pendResult_storePackVal {s s' : Store H} {f : Frame} {t : IntType} {sz : PackSize}
    {ao : V2.MemArg} {i : BitVec 32} {k : BitVec t.width} {a : List Val} {y : Admin}
    {L : List Admin} (hy : PendOp y)
    (hc : [constI32 i, Admin.plain (.intConst t k), Admin.plain (.intStore t (some sz) ao)] =
      vals a ++ y :: L) :
    PendResult s f a y L ⟨s', f, []⟩ := by
  have e : [constI32 i, Admin.plain (.intConst t k), Admin.plain (.intStore t (some sz) ao)] =
    vals [i32V i, .num ⟨.int t, k⟩] ++ .plain (.intStore t (some sz) ao) :: [] := rfl
  obtain ⟨rfl, rfl, rfl⟩ := vals_cons_inj20 rfl hy.isVal (e ▸ hc)
  exact ⟨[], i, _, rfl, rfl, .inl rfl⟩

/-- `ctxt-instrs` at a pending operator: the inner code starts with it. -/
theorem pendResult_ctx {P : Profile} {host : HostSemantics H} {s s' : Store H} {f f' : Frame}
    {vs : List Val} {is is' rest : List Admin} (hstep : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩)
    (ih : ∀ {a : List Val} {y : Admin} {L : List Admin}, PendOp y → is = vals a ++ y :: L →
      PendResult s f a y L ⟨s', f', is'⟩)
    {a : List Val} {y : Admin} {L : List Admin} (hy : PendOp y)
    (hc : vals vs ++ is ++ rest = vals a ++ y :: L) :
    PendResult s f a y L ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  obtain ⟨p, z, q, rfl, hz⟩ := exists_split20 hstep.not_allVals
  have e : vals vs ++ (vals p ++ z :: q) ++ rest = vals (vs ++ p) ++ z :: (q ++ rest) := by simp
  obtain ⟨rfl, rfl, rfl⟩ := vals_cons_inj20 hz hy.isVal (e ▸ hc)
  exact pendResult_append (ih hy rfl)

/-- **Every step from `val* y rest`, `y` a pending operator, is that operator**: it consumes the
last two values, keeps the frame, and leaves `rest` behind, or traps, and then `y` is out of
range. -/
theorem step_pendHead {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') :
    ∀ {a : List Val} {y : Admin} {L : List Admin}, PendOp y → c.code = vals a ++ y :: L →
      PendResult c.store c.frame a y L c' := by
  induction h with
  | pure hp => exact fun hy hc => (pend_absurd hy hc fun _ hy' => pure_find_not_pend hp hy').elim
  | read hr => exact fun hy hc => (pend_absurd hy hc fun _ hy' => read_find_not_pend hr hy').elim
  | ctxtInstrs hstep _ ih => exact pendResult_ctx hstep ih
  | ctxtLabel => exact fun hy hc => (not_pend_of_find hy hc (find_cons_nonval _ rfl)
      not_pendOp_label).elim
  | ctxtFrame => exact fun hy hc => (not_pend_of_find hy hc (find_cons_nonval _ rfl)
      not_pendOp_frame).elim
  | tableSetTrap ha ht hlen => exact pendResult_tableSetTrap ha ht hlen
  | tableSetVal => exact pendResult_tableSetVal
  | storePackTrap ha hm hlen => exact pendResult_storePackTrap ha hm hlen
  | storePackVal => exact pendResult_storePackVal
  | _ => exact fun hy hc => (pend_absurd hy hc fun _ hy' => by
      rcases hy' with ⟨x, rfl⟩ | rfl <;> simp [isVal_plain, Admin.val?, store8, memarg0]).elim

/-! ## Preservation -/

/-- One label around `Plain20` code. -/
theorem plain20_label1 {s : Store H} {f : Frame} (n : Nat) (cont : List V2.Instr)
    {body : List Admin} (hb : Plain20 s f body) : Plain20 s f [.label n cont body] :=
  .label [] n cont body [] hb

/-- One frame around `Plain20` code. -/
theorem plain20_frame1 {s : Store H} {f fi : Frame} (n : Nat) {body : List Admin}
    (hb : Plain20 s fi body) : Plain20 s f [.frame n fi body] := .frame [] n fi body [] hb

theorem plain20_val1 {s : Store H} {f : Frame} (v : Val) : Plain20 s f [v.toAdmin] := .allVals [v]

theorem plain20_instr1 {s : Store H} {f : Frame} (i : V2.Instr) : Plain20 s f [.plain i] :=
  plain20_expression [i]

/-- A result is `Plain20`. -/
theorem plain20_result {s : Store H} {f : Frame} (r : Result) : Plain20 s f r.toAdmin := by
  cases r with
  | values vs => exact .allVals vs
  | trap => exact .trap [] []

/-- **Every pure step produces `Plain20` code**, at any state. -/
theorem plain20_pureStep {P : Profile} {s : Store H} {f : Frame} {is is' : List Admin}
    (h : PureStep P is is') : Plain20 s f is' := by
  cases h with
  | selectTrue _ => exact plain20_val1 _
  | selectFalse _ _ _ => exact plain20_val1 _
  | labelVals => exact .allVals _
  | brZero _ _ => exact plain20_vals_expr _ _
  | brSucc _ => exact plain20_vals_expr _ [_]
  | frameVals _ | returnFrame _ => exact .allVals _
  | returnLabel => exact plain20_vals_expr _ [_]
  | localTee => exact plain20_vals_expr [_, _] [_]
  | _ => exact plain20_of_flatOk (by simp [flatOk, isVal_plain, Admin.val?, isFlatHead])

/-- `table.set` from a bulk table rule is in range. -/
theorem setOk_of {s : Store H} {f : Frame} {x : TableIdx} {i n : BitVec 32} {ti : TableInst}
    (ht : (⟨s, f⟩ : State H).table? x = some ti) (hb : i.toNat + n.toNat ≤ ti.refs.length)
    (hn : n ≠ 0) : PendOk s f (.plain (.tableSet x)) i := by
  refine ⟨fun x' hx' a ti' ha ht' => ?_, fun h => by simp [store8] at h⟩
  cases hx'
  have : ti' = ti := by simpa [State.table?, ha, ht'] using ht
  subst this
  have : n.toNat ≠ 0 := fun h0 => hn (BitVec.eq_of_toNat_eq (by simpa using h0))
  omega

/-- `table.fill-succ`'s result is a pending in-range `table.set`. -/
theorem plain20_tableFillSucc {s : Store H} {f : Frame} {x : TableIdx} {i n : BitVec 32} {v : Val}
    {ti : TableInst} (ht : (⟨s, f⟩ : State H).table? x = some ti)
    (hb : i.toNat + n.toNat ≤ ti.refs.length) (hn : n ≠ 0) :
    Plain20 s f [constI32 i, v.toAdmin, .plain (.tableSet x),
      constI32 (i + 1), v.toAdmin, constI32 (n - 1), .plain (.tableFill x)] :=
  .pend [] i v _ [i32V (i + 1), v, i32V (n - 1)] [.tableFill x] (.inl ⟨x, rfl⟩) (setOk_of ht hb hn)

/-- `table.init-succ`'s result is a pending in-range `table.set`. -/
theorem plain20_tableInitSucc {s : Store H} {f : Frame} {x : TableIdx} {y : ElemIdx}
    {j i n : BitVec 32} {ti : TableInst} {r : Ref} (ht : (⟨s, f⟩ : State H).table? x = some ti)
    (hb : j.toNat + n.toNat ≤ ti.refs.length) (hn : n ≠ 0) :
    Plain20 s f [constI32 j, aref r, .plain (.tableSet x),
      constI32 (j + 1), constI32 (i + 1), constI32 (n - 1), .plain (.tableInit x y)] :=
  .pend [] j (.ref r) _ [i32V (j + 1), i32V (i + 1), i32V (n - 1)] [.tableInit x y]
    (.inl ⟨x, rfl⟩) (setOk_of ht hb hn)

/-- `memory.fill-succ`'s first byte is in range. -/
theorem pendOk_store8 {s : Store H} {f : Frame} {i n : BitVec 32} {mi : MemInst}
    (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi) (hb : i.toNat + n.toNat ≤ mi.bytes.size)
    (hn : n ≠ 0) : PendOk s f store8 i := by
  refine ⟨fun x h => by simp [store8] at h, fun _ a mi' ha hm' => ?_⟩
  have e : mi' = mi := by simpa [State.mem?, ha, hm'] using hm
  have h0 : n.toNat ≠ 0 := fun h0 => hn (BitVec.eq_of_toNat_eq (by simpa using h0))
  rw [e]
  simp only [effAddr, memarg0]
  omega

/-- **Every read step produces `Plain20` code** at its state. -/
theorem plain20_readStep {s : Store H} {f : Frame} {is is' : List Admin}
    (h : ReadStep s f is is') : Plain20 s f is' := by
  cases h with
  | block _ _ | loop _ _ => exact plain20_label1 _ _ (plain20_vals_expr _ _)
  | callAddr _ _ _ => exact plain20_frame1 _ (plain20_label1 _ _ (plain20_expression _))
  | localGet _ | globalGet _ => exact plain20_val1 _
  | tableGetVal _ _ => exact plain20_val1 (.ref _)
  | tableFillSucc ht hb hn => exact plain20_tableFillSucc ht hb hn
  | tableInitSucc ht _ hb hn _ => exact plain20_tableInitSucc ht hb.2 hn
  | memoryFillSucc hm hb hn =>
    exact .pend [] _ _ _ [i32V (_ + 1), _, i32V (_ - 1)] [.memoryFill] (.inr rfl)
      (pendOk_store8 hm hb hn)
  | _ => exact plain20_of_flatOk (by
      simp [flatOk, isVal_plain, Admin.val?, isFlatHead, isPlainA, store8, load8u])

/-- Two values at the end of two equal value lists. -/
theorem append_two_inj {l₁ l₂ : List Val} {a b c d : Val} (h : l₁ ++ [a, b] = l₂ ++ [c, d]) :
    a = c := by
  have := congrArg List.reverse h
  simp at this
  exact this.2.1

/-- `Plain20` through `ctxt-instrs`, given it for the inner step. -/
theorem plain20_ctx {P : Profile} {host : HostSemantics H} {s s' : Store H} {f f' : Frame}
    {vs : List Val} {is is' rest : List Admin} (hstep : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩)
    (hp : Plain20 s f (vals vs ++ is ++ rest))
    (ih : Plain20 s f is → Plain20 s' f' is') : Plain20 s' f' (vals vs ++ is' ++ rest) := by
  obtain ⟨p, y, q, rfl, hy⟩ := exists_split20 hstep.not_allVals
  have e : vals vs ++ (vals p ++ y :: q) ++ rest = vals (vs ++ p) ++ y :: (q ++ rest) := by simp
  rcases (e ▸ hp).split hy with ⟨⟨js, hjs⟩, hh⟩ | ⟨us, i, v, ws, js, hus, hpo, hM, hok⟩
  · obtain ⟨js₁, js₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.1 hjs.symm
    rw [← h₁] at ih
    rw [← h₂]
    exact plain20_wrap (ih (plain20_build p hy hh js₁)) vs js₂
  · obtain ⟨a', i', w, rfl, hf, hc⟩ := step_pendHead hstep hpo rfl
    simp only at hf hc
    subst hf
    have hi : i32V i' = i32V i := append_two_inj (l₁ := vs ++ a') (by rw [List.append_assoc]; exact hus)
    cases hi
    rcases hc with rfl | ⟨-, hn⟩
    · have e' : vals vs ++ (vals a' ++ q) ++ rest = vals (vs ++ a') ++ (q ++ rest) := by simp
      rw [e', hM, ← List.append_assoc, ← vals_append]
      exact plain20_vals_expr _ _
    · exact absurd hok hn

/-- **Every V2 step preserves `Plain20`.** -/
theorem plain20_step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hp : Plain20 c.store c.frame c.code) :
    Plain20 c'.store c'.frame c'.code := by
  induction h with
  | pure hs => exact plain20_pureStep hs
  | read hs => exact plain20_readStep hs
  | ctxtInstrs hs _ ih => exact plain20_ctx hs hp ih
  | ctxtLabel _ ih => exact plain20_label1 _ _ (ih hp.label_body)
  | ctxtFrame _ ih => exact plain20_frame1 _ (ih hp.frame_body)
  | callAddrHost _ _ _ _ => exact plain20_result _
  | callAddrHostDiv _ _ _ _ => exact hp
  | _ => exact plain20_of_flatOk (by simp [flatOk, isVal_plain, Admin.val?, isFlatHead])

/-- **Every V2 run preserves `Plain20`.** -/
theorem plain20_steps {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') (hp : Plain20 c.store c.frame c.code) :
    Plain20 c'.store c'.frame c'.code := by
  induction h with
  | refl => exact hp
  | tail _ h₂ ih => exact plain20_step h₂ ih

/-- **The code of an invocation is `Plain20`.** -/
theorem plain20_invoke {s : Store H} {f : Frame} (args : List Val) (a : FuncAddr) :
    Plain20 s f (vals args ++ [.callAddr a]) := .callAddr args a []

/-! ## The inner code of each context -/

/-- `Plain20`, or a pending-operator head: what the inner code of a context satisfies. -/
def Tail20 (s : Store H) (f : Frame) (l : List Admin) : Prop :=
  Plain20 s f l ∨ ∃ p y q, l = vals p ++ y :: q ∧ PendOp y

/-- `Tail20` passes to the inner code of `ctxt-instrs`. -/
theorem tail20_ctx {s : Store H} {f : Frame} {vs : List Val} {is rest : List Admin}
    (hne : is.all Admin.isVal = false) (h : Tail20 s f (vals vs ++ is ++ rest)) : Tail20 s f is := by
  obtain ⟨p, y, q, rfl, hy⟩ := exists_split20 hne
  have e : vals vs ++ (vals p ++ y :: q) ++ rest = vals (vs ++ p) ++ y :: (q ++ rest) := by simp
  rcases h with hp | ⟨p', y', q', hc, hpo⟩
  · rcases (e ▸ hp).split hy with ⟨⟨js, hjs⟩, hh⟩ | ⟨_, _, _, _, _, -, hpo, -, -⟩
    · obtain ⟨js₁, js₂, -, h₁, -⟩ := List.map_eq_append_iff.1 hjs.symm
      exact .inl (h₁ ▸ plain20_build p hy hh js₁)
    · exact .inr ⟨p, y, q, rfl, hpo⟩
  · obtain ⟨-, rfl, -⟩ := vals_cons_inj20 hy hpo.isVal ((e ▸ hc :))
    exact .inr ⟨p, y, q, rfl, hpo⟩

/-- `Tail20` of a one-element label is `Plain20` of its body. -/
theorem tail20_label {s : Store H} {f : Frame} {n : Nat} {cont : List V2.Instr} {body : List Admin}
    (h : Tail20 s f [.label n cont body]) : Plain20 s f body := by
  rcases h with hp | ⟨p, y, q, hc, hpo⟩
  · exact hp.label_body
  · have e : [(.label n cont body : Admin)] = vals [] ++ Admin.label n cont body :: [] := rfl
    obtain ⟨-, rfl, -⟩ := vals_cons_inj20 rfl hpo.isVal (e ▸ hc)
    exact absurd hpo not_pendOp_label

/-- `Tail20` of a one-element frame is `Plain20` of its body, in the inner frame. -/
theorem tail20_frame {s : Store H} {f fi : Frame} {n : Nat} {body : List Admin}
    (h : Tail20 s f [.frame n fi body]) : Plain20 s fi body := by
  rcases h with hp | ⟨p, y, q, hc, hpo⟩
  · exact hp.frame_body
  · have e : [(.frame n fi body : Admin)] = vals [] ++ Admin.frame n fi body :: [] := rfl
    obtain ⟨-, rfl, -⟩ := vals_cons_inj20 rfl hpo.isVal (e ▸ hc)
    exact absurd hpo not_pendOp_frame

/-- `Plain20` code is `Tail20`. -/
theorem Plain20.tail {s : Store H} {f : Frame} {l : List Admin} (h : Plain20 s f l) :
    Tail20 s f l := .inl h

/-- At a non-value that is not a pending operator, `Tail20` code has a plain suffix. -/
theorem Tail20.plain_after {s : Store H} {f : Frame} {a : List Val} {y : Admin} {M : List Admin}
    (h : Tail20 s f (vals a ++ y :: M)) (hy : y.isVal = false) (hs : ¬ PendOp y) :
    ∃ is, M = expression is := by
  rcases h with hp | ⟨p, x, q, hc, hpo⟩
  · rcases hp.split hy with ⟨hM, -⟩ | ⟨_, _, _, _, _, -, hpo, -, -⟩
    · exact hM
    · exact absurd hpo hs
  · obtain ⟨-, rfl, -⟩ := vals_cons_inj20 hy hpo.isVal hc
    exact absurd hpo hs

end Silmaril.Wasm.SpecTec.Sim20.Whole
