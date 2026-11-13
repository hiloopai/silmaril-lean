module

public import Silmaril.Wasm.Execution.Memory
public import Mathlib.Order.Disjoint
public import Silmaril.Wasm.V1.Instructions
public import Silmaril.Wasm.Execution.Runtime

/-!
# The Wasm Logic assertion language

Figure 5 of Watt, Maksimović, Krishnaswami and Gardner. An assertion is a pair
of a *stack assertion* — a list of terms, one per operand, which is legitimate
because WebAssembly's type system fixes the stack shape at every program point —
and a *heap assertion* combining predicate logic with separation logic over
`AHeap`.

We embed the assertion language shallowly: terms are Lean functions of an
abstract variable store, pure assertions are Lean propositions over that store,
and existential quantification is a Lean binder. This departs from the paper in
two ways, both recorded in `docs/projects/wasm-wasi.md`.

* Existentials range over an arbitrary `Type`, not only over WebAssembly
  constants. The paper's own B-tree proofs quantify over lists and sets of keys,
  which its grammar does not actually provide.
* The paper's syntactic side condition `fv(H) ∩ mv(e*) = ∅` of the `[frame]`
  rule becomes the semantic `HAssert.Indep`: insensitivity of the assertion to
  the variables an instruction sequence may modify. A syntactic assertion with
  no free variable in `mv(e*)` satisfies it, so this is the weaker requirement.

## The abstract heap

### Abstract heaps and their separation algebra

Wasm Logic's spatial assertions do not denote WebAssembly memories directly.
In a WebAssembly linear memory the existence of address `x + 1` implies the
existence of address `x`, but owning `x + 1` must not imply owning `x`. Watt
et al. (§5) therefore interpret heap assertions into *abstract* heaps: a
partial map from byte addresses to bytes, together with an optional ownership
of the memory's page count. Reification (`Silmaril.Wasm.Logic.V1.Reify`) then
relates an abstract heap to a concrete memory.

The page-count component behaves like the "free set" resource of a permission
logic: owning it is permission to call `memory.grow`.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp ExternType FuncType GlobalType IntUnOp Limits MemoryType PackSize ResultType TableType ValType
open Silmaril.Wasm.V1

open Silmaril.Wasm.Execution

/-- A partial map from byte addresses to bytes, plus optional ownership of the
number of allocated pages. -/
structure AHeap where
  cells : Nat → Option Memory.Byte
  size : Option Nat

namespace AHeap

theorem ext {h h' : AHeap} (cells : ∀ i, h.cells i = h'.cells i)
    (size : h.size = h'.size) : h = h' := by
  cases h; cases h'
  simp only [AHeap.mk.injEq]
  exact ⟨funext cells, size⟩

/-- The empty heap: no addresses owned, no page-count ownership. -/
def emp : AHeap := ⟨fun _ => none, none⟩

/-- Ownership of a single byte. -/
def single (a : Nat) (b : Memory.Byte) : AHeap :=
  ⟨fun i => if i = a then some b else none, none⟩

/-- Ownership of a contiguous byte segment starting at `a`. -/
def ofBytes (a : Nat) (bs : List Memory.Byte) : AHeap :=
  ⟨fun i => if a ≤ i then bs[i - a]? else none, none⟩

/-- Ownership of the page count alone. -/
def pages (n : Nat) : AHeap := ⟨fun _ => none, some n⟩

/-- Two abstract heaps can be combined: disjoint domains, and at most one of
them owns the page count. -/
def Disj (h h' : AHeap) : Prop :=
  (∀ i, h.cells i = none ∨ h'.cells i = none) ∧ (h.size = none ∨ h'.size = none)

/-- The combination of two abstract heaps; meaningful when they are `Disj`. -/
def union (h h' : AHeap) : AHeap :=
  ⟨fun i => (h.cells i).or (h'.cells i), h.size.or h'.size⟩

instance : Union AHeap := ⟨union⟩

@[simp] theorem union_cells (h h' : AHeap) (i : Nat) :
    (h ∪ h').cells i = (h.cells i).or (h'.cells i) := rfl

@[simp] theorem union_size (h h' : AHeap) : (h ∪ h').size = h.size.or h'.size := rfl

theorem Disj.symm {h h' : AHeap} (d : Disj h h') : Disj h' h :=
  ⟨fun i => (d.1 i).symm, d.2.symm⟩

theorem disj_comm {h h' : AHeap} : Disj h h' ↔ Disj h' h := ⟨Disj.symm, Disj.symm⟩

@[simp] theorem disj_emp (h : AHeap) : Disj h emp := ⟨fun _ => .inr rfl, .inr rfl⟩

@[simp] theorem emp_disj (h : AHeap) : Disj emp h := ⟨fun _ => .inl rfl, .inl rfl⟩

@[simp] theorem union_emp (h : AHeap) : h ∪ emp = h :=
  AHeap.ext (fun i => by simp [emp]) (by simp [emp])

@[simp] theorem emp_union (h : AHeap) : emp ∪ h = h :=
  AHeap.ext (fun _ => rfl) rfl

theorem union_comm {h h' : AHeap} (d : Disj h h') : h ∪ h' = h' ∪ h :=
  AHeap.ext
    (fun i => by rcases d.1 i with hi | hi <;> simp [hi])
    (by rcases d.2 with hi | hi <;> simp [hi])

theorem union_assoc (h₁ h₂ h₃ : AHeap) : (h₁ ∪ h₂) ∪ h₃ = h₁ ∪ (h₂ ∪ h₃) :=
  AHeap.ext (fun i => by simp [Option.or_assoc]) (by simp [Option.or_assoc])

theorem disj_union_left {h₁ h₂ h₃ : AHeap} (d : Disj (h₁ ∪ h₂) h₃) : Disj h₁ h₃ := by
  refine ⟨fun i => ?_, ?_⟩
  · rcases d.1 i with hi | hi
    · exact .inl (by cases e : h₁.cells i <;> simp [e] at hi ⊢)
    · exact .inr hi
  · rcases d.2 with hi | hi
    · exact .inl (by cases e : h₁.size <;> simp [e] at hi ⊢)
    · exact .inr hi

theorem disj_union_right {h₁ h₂ h₃ : AHeap} (d : Disj (h₁ ∪ h₂) h₃) : Disj h₂ h₃ := by
  refine ⟨fun i => ?_, ?_⟩
  · rcases d.1 i with hi | hi
    · exact .inl (by cases e : h₁.cells i <;> cases e' : h₂.cells i <;> simp_all)
    · exact .inr hi
  · rcases d.2 with hi | hi
    · exact .inl (by cases e : h₁.size <;> cases e' : h₂.size <;> simp_all)
    · exact .inr hi

theorem disj_union {h₁ h₂ h₃ : AHeap} (d₁ : Disj h₁ h₃) (d₂ : Disj h₂ h₃) :
    Disj (h₁ ∪ h₂) h₃ := by
  refine ⟨fun i => ?_, ?_⟩
  · rcases d₁.1 i with hi | hi
    · rcases d₂.1 i with hj | hj
      · exact .inl (by simp [hi, hj])
      · exact .inr hj
    · exact .inr hi
  · rcases d₁.2 with hi | hi
    · rcases d₂.2 with hj | hj
      · exact .inl (by simp [hi, hj])
      · exact .inr hj
    · exact .inr hi

end AHeap

end Silmaril.Wasm.Logic.V1

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp ExternType FuncType GlobalType IntUnOp Limits MemoryType PackSize ResultType TableType ValType
open Silmaril.Wasm.V1

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

/-- Logical, local and global variables. Local and global variables are named
by their index, as in the paper's `lᵢ` and `gᵢ`. -/
inductive Var where
  | log (name : Nat)
  | loc (index : Nat)
  | glob (index : Nat)
  deriving DecidableEq, Repr

/-- The set of local and global variables, which program execution may change. -/
def Var.IsProgram : Var → Prop
  | .log _ => False
  | .loc _ | .glob _ => True

/-- An abstract variable store. Unlike the paper's partial map we use a total
map; "variable `ν` is not mentioned" is expressed by an assertion not depending
on it, rather than by `ν` being outside the domain. -/
abbrev Sto := Var → Value

def Sto.update (ρ : Sto) (x : Var) (v : Value) : Sto := fun y => if y = x then v else ρ y

@[simp] theorem Sto.update_self (ρ : Sto) (x : Var) (v : Value) :
    ρ.update x v x = v := by simp [Sto.update]

@[simp] theorem Sto.update_other (ρ : Sto) {x y : Var} (v : Value) (h : y ≠ x) :
    ρ.update x v y = ρ y := by simp [Sto.update, h]

/-- A term: the paper's `τ`, shallowly. -/
abbrev Term (α : Type) := Sto → α

/-- Insensitivity of a term to the variables in `X`. -/
def Term.Indep {α : Type} (X : Set Var) (τ : Term α) : Prop :=
  ∀ ρ ρ', (∀ x, x ∉ X → ρ x = ρ' x) → τ ρ = τ ρ'

/-- The instruction pushing a given runtime value. -/
def constInstr : Value → Instr
  | ⟨.int t, bits⟩ => .intConst t bits
  | ⟨.float t, bits⟩ => .floatConst t bits

/-- The term denoting the value of local variable `i`. -/
def Term.local_ (i : Nat) : Term Value := fun ρ => ρ (.loc i)

/-- The term denoting the value of global variable `i`. -/
def Term.global (i : Nat) : Term Value := fun ρ => ρ (.glob i)

def Term.int (t : IntType) (x : Term (BitVec t.width)) : Term Value := fun ρ => .int t (x ρ)

def Term.float (t : FloatType) (x : Term (BitVec t.width)) : Term Value := fun ρ => .float t (x ρ)

/-- i32 is the default domain of the paper's terms. -/
def Term.i32 (x : Term (BitVec 32)) : Term Value := Term.int .i32 x

def Term.const (v : Value) : Term Value := fun _ => v

/-- Heap assertions: the paper's `Aph`. -/
abbrev HAssert := Sto → AHeap → Prop

namespace HAssert

/-- A pure assertion: no resource, a condition on the variable store. -/
def pure (φ : Sto → Prop) : HAssert := fun ρ _ => φ ρ

def false_ : HAssert := pure fun _ => False

def emp : HAssert := fun _ h => h = AHeap.emp

def and (H H' : HAssert) : HAssert := fun ρ h => H ρ h ∧ H' ρ h

def or (H H' : HAssert) : HAssert := fun ρ h => H ρ h ∨ H' ρ h

/-- Separating conjunction. -/
def star (H H' : HAssert) : HAssert :=
  fun ρ h => ∃ h₁ h₂, AHeap.Disj h₁ h₂ ∧ h = h₁ ∪ h₂ ∧ H ρ h₁ ∧ H' ρ h₂

/-- Existential quantification over an arbitrary Lean type. -/
def ex {α : Type} (f : α → HAssert) : HAssert := fun ρ h => ∃ a, f a ρ h

/-- The paper's iterated star `⊛_{lo ≤ i < hi}`, at fixed bounds. -/
def iterRange (lo hi : Nat) (f : Nat → HAssert) : HAssert :=
  (List.range' lo (hi - lo)).foldr (fun i acc => star (f i) acc) emp

/-- The paper's iterated star `⊛_{τ₁ ≤ i < τ₂}`. -/
def iter (lo hi : Term Nat) (f : Nat → HAssert) : HAssert :=
  fun ρ h => iterRange (lo ρ) (hi ρ) f ρ h

/-- `emp` conjoined with a pure assertion, the shape every rule for a
heap-independent instruction uses. -/
def empAnd (φ : Sto → Prop) : HAssert := and emp (pure φ)

/-- Ownership of a single byte, the paper's `τ₁ ↦ τ₂`. -/
def cell (a : Term Nat) (b : Term Memory.Byte) : HAssert :=
  fun ρ h => h = AHeap.single (a ρ) (b ρ)

/-- Ownership of a byte of unspecified content, the paper's `τ ↦ -`. -/
def cellAny (a : Term Nat) : HAssert := ex fun b : Memory.Byte => cell a fun _ => b

/-- Ownership of a contiguous byte segment. -/
def seg (a : Term Nat) (bs : Term (List Memory.Byte)) : HAssert :=
  fun ρ h => h = AHeap.ofBytes (a ρ) (bs ρ)

/-- The type-annotated cell assertion `τ₁ ↦ₜ τ₂`: the little-endian encoding of
a numeric value, over as many bytes as its type occupies. -/
def cellNum (t : NumType) (a : Term Nat) (v : Term (BitVec t.width)) : HAssert :=
  seg a fun ρ => (Memory.encodeLE (t.width / 8) (v ρ).toNat).toList

/-- `τ₁ ↦ₜ -`: ownership of a `t`-sized slot with unspecified contents. -/
def cellNumAny (t : NumType) (a : Term Nat) : HAssert :=
  ex fun x : BitVec t.width => cellNum t a fun _ => x

/-- Ownership of the memory's page count, the paper's `size(τ)`. -/
def size (n : Term Nat) : HAssert := fun ρ h => h = AHeap.pages (n ρ)

/-- Insensitivity to the variables in `X`: the semantic form of the paper's
syntactic `fv(H) ∩ X = ∅`. -/
def Indep (X : Set Var) (H : HAssert) : Prop :=
  ∀ ρ ρ' h, (∀ x, x ∉ X → ρ x = ρ' x) → (H ρ h ↔ H ρ' h)

end HAssert

/-- Wasm Logic assertions: a stack part and a heap part, closed under `∃`. -/
abbrev Assert := Sto → List Value → AHeap → Prop

namespace Assert

/-- The paper's `(S | H)`. -/
def mk (S : List (Term Value)) (H : HAssert) : Assert :=
  fun ρ vs h => vs = S.map (fun τ => τ ρ) ∧ H ρ h

def ex {α : Type} (f : α → Assert) : Assert := fun ρ vs h => ∃ a, f a ρ vs h

/-- The paper's `(S | emp)`. -/
def stack (S : List (Term Value)) : Assert := mk S HAssert.emp

/-- The paper's `(S | emp ∧ φ)`. -/
def stackIf (S : List (Term Value)) (φ : Sto → Prop) : Assert := mk S (HAssert.empAnd φ)

def false_ : Assert := fun _ _ _ => False

/-- The paper's `⊗`: distribute a heap frame through an assertion. -/
def frame (P : Assert) (Hf : HAssert) : Assert :=
  fun ρ vs h => ∃ h₁ h₂, AHeap.Disj h₁ h₂ ∧ h = h₁ ∪ h₂ ∧ P ρ vs h₁ ∧ Hf ρ h₂

/-- Extend the bottom of the stack assertion: the `[extension]` rule's operator. -/
def extend (S : List (Term Value)) (P : Assert) : Assert :=
  fun ρ vs h => ∃ vs', vs = S.map (fun τ => τ ρ) ++ vs' ∧ P ρ vs' h

/-- Entailment, the paper's `P ⇒ Q`. -/
def Entails (P Q : Assert) : Prop := ∀ ρ vs h, P ρ vs h → Q ρ vs h

/-- The paper's `Pₙ` notation: the stack part has exactly `n` entries. -/
def StackLen (P : Assert) (n : Nat) : Prop := ∀ ρ vs h, P ρ vs h → vs.length = n

/-- Insensitivity to the variables in `X`, as for heap assertions. -/
def Indep (X : Set Var) (P : Assert) : Prop :=
  ∀ ρ ρ' vs h, (∀ x, x ∉ X → ρ x = ρ' x) → (P ρ vs h ↔ P ρ' vs h)

theorem Entails.refl (P : Assert) : Entails P P := fun _ _ _ h => h

theorem Entails.trans {P Q R : Assert} (h : Entails P Q) (h' : Entails Q R) : Entails P R :=
  fun ρ vs hp hq => h' ρ vs hp (h ρ vs hp hq)

@[simp] theorem stackLen_mk (S : List (Term Value)) (H : HAssert) :
    StackLen (mk S H) S.length := by
  rintro ρ vs h ⟨rfl, -⟩; simp

end Assert

mutual
/-- The local and global variables an instruction may assign to: the paper's
`mv(e*)`. A call is over-approximated as modifying every global, because the
callee's effect on the globals is not visible in its specification. -/
def Instr.modified : Instr → Set Var
  | .localSet i | .localTee i => {Var.loc i.toNat}
  | .globalSet i => {Var.glob i.toNat}
  | .block _ body | .loop _ body => Expr.modified body
  | .if_ _ left right => Expr.modified left ∪ Expr.modified right
  | .call _ | .callIndirect _ => {x | ∃ j, x = Var.glob j}
  | _ => ∅
/-- The local and global variables an instruction sequence may assign to. -/
def Expr.modified : List Instr → Set Var
  | [] => ∅
  | i :: rest => Instr.modified i ∪ Expr.modified rest
end

@[simp] theorem Expr.modified_nil : Expr.modified [] = ∅ := rfl

@[simp] theorem Expr.modified_cons (i : Instr) (rest : Expr) :
    Expr.modified (i :: rest) = Instr.modified i ∪ Expr.modified rest := rfl

@[simp] theorem Expr.modified_single (i : Instr) : Expr.modified [i] = Instr.modified i := by
  simp

theorem Expr.modified_append (e₁ e₂ : Expr) :
    Expr.modified (e₁ ++ e₂) = Expr.modified e₁ ∪ Expr.modified e₂ := by
  induction e₁ with
  | nil => simp
  | cons i rest ih => simp [ih, Set.union_assoc]

theorem Expr.subset_modified_append_left (e₁ e₂ : Expr) :
    Expr.modified e₁ ⊆ Expr.modified (e₁ ++ e₂) := by
  simp [Expr.modified_append]

theorem Expr.subset_modified_append_right (e₁ e₂ : Expr) :
    Expr.modified e₂ ⊆ Expr.modified (e₁ ++ e₂) := by
  simp [Expr.modified_append]

@[simp] theorem Instr.modified_block (bt : Silmaril.Wasm.V1.BlockType) (body : Expr) :
    Instr.modified (.block bt body) = Expr.modified body := rfl

@[simp] theorem Instr.modified_loop (bt : Silmaril.Wasm.V1.BlockType) (body : Expr) :
    Instr.modified (.loop bt body) = Expr.modified body := rfl

@[simp] theorem Instr.modified_if (bt : Silmaril.Wasm.V1.BlockType) (left right : Expr) :
    Instr.modified (.if_ bt left right) = Expr.modified left ∪ Expr.modified right := rfl

mutual
/-- A logical variable is never modified by execution. -/
theorem Instr.log_not_modified (i : Instr) (x : Nat) : Var.log x ∉ Instr.modified i := by
  match i with
  | .block _ body | .loop _ body => exact Expr.log_not_modified body x
  | .if_ _ left right =>
      rintro (h | h)
      · exact Expr.log_not_modified left x h
      · exact Expr.log_not_modified right x h
  | .localSet _ | .localTee _ | .globalSet _ => rintro h; exact Var.noConfusion h
  | .call _ | .callIndirect _ => rintro ⟨_, h⟩; exact Var.noConfusion h
  | .nop | .unreachable | .drop | .select | .br _ | .brIf _ | .brTable _ _ | .return_
  | .localGet _ | .globalGet _ | .intLoad _ _ _ | .floatLoad _ _ | .intStore _ _ _
  | .floatStore _ _ | .memorySize | .memoryGrow | .intConst _ _ | .floatConst _ _
  | .intUnOp _ _ | .intBinOp _ _ | .intTestOp _ _ | .intRelOp _ _ | .floatUnOp _ _
  | .floatBinOp _ _ | .floatRelOp _ _ | .convert _ => exact id

/-- A logical variable is never modified by execution. -/
theorem Expr.log_not_modified (e : Expr) (x : Nat) : Var.log x ∉ Expr.modified e := by
  match e with
  | [] => exact id
  | i :: rest =>
      rintro (h | h)
      · exact Instr.log_not_modified i x h
      · exact Expr.log_not_modified rest x h
end

/-- Agreement outside the variables an instruction sequence modifies implies
agreement on the logical variables. -/
theorem Sto.not_isProgram_of_agree {e : Expr} {ρ ρ' : Sto}
    (agree : ∀ x, x ∉ Expr.modified e → ρ' x = ρ x) (x : Var) (h : ¬ x.IsProgram) :
    ρ' x = ρ x := by
  cases x with
  | log k => exact agree _ (Expr.log_not_modified e k)
  | loc k => exact absurd trivial h
  | glob k => exact absurd trivial h

end Silmaril.Wasm.Logic.V1
