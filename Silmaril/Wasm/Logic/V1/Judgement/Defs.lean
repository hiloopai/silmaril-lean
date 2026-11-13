module

public import Silmaril.Wasm.Logic.V1.Assertions.Defs
public import Silmaril.Wasm.Logic.V1.BigStep.Thms

/-!
# Wasm Logic: the judgement and its meaning

Three parts of Watt et al. (ECOOP 2019), in order: reification of abstract state
(Figure 16), the semantic triple `Valid` (Figure 17) and the proof rules `Triple`
(Figures 6 to 11), with the `[function]` and `[module]` rules `FuncRule` and
`ModuleSpecs`.

## Reification

The second stage of the interpretation of Figure 16 of Watt et al.: an abstract
variable store and an abstract heap are *reified* by a WebAssembly store and
frame when the owned addresses agree with the linear memory, the page-count
resource (if owned) agrees with the memory's size, the local and global
variables agree with the frame and the store, and the module's functions are the
ones the context assumes.

Three conditions are ours rather than the paper's.

* `ReifiesMem` requires the module to have a linear memory. The paper's `maddr`
  is a `nat option` and the two memory conjuncts of `reifies_s` are guarded by
  ownership, so an instance with no memory reifies against any heap owning no
  cell and no page count. Ours asserts the memory's existence outright, which
  strengthens a hypothesis of `Valid`: the soundness theorems say nothing about
  a memory-less module. Every module the logic is used on has one.
* `ReifiesGlobals` is stated against a module instance whose global addresses
  are pairwise distinct. The paper's instances come from instantiating a single
  encapsulated module, where this holds; we need it explicitly because a
  `global.set` must not silently change another global variable of the logic.
* The paper's `inst` is a separate index of the judgement. Our frames carry
  their module instance, so `inst` is `Frame.module` throughout.

## The semantic triple

Figure 17 of Watt et al. A triple holds when, for every execution of `code`
from a state satisfying the precondition, the execution does not trap, and the
final state satisfies the postcondition if it terminated normally, the `l`-th
label assertion if it is branching to label `l`, and the return assertion if it
is returning.

Framing appears in three places, exactly as in the paper: in the heap (`hf`),
in the operand stack (`vf`), and — in the paper — in the label context. Our
`BigStep` has no label index, so the third is implicit: the judgement only
constrains results that branch to a label of `L`, and `Triple.context` may
enlarge `L`.

Two differences from Figure 17 are recorded here and in `docs/projects/wasm-wasi.md`.

* A branch or return result discards an arbitrary prefix of the operand stack,
  not exactly the frame `vf`. The paper's semantics discards the whole stack
  frame at a branch automatically (§5: "the stack frame ... is discarded in case
  of the Break and Return results"); ours carries the stack along, and the
  target label discards everything below the arity it takes. Requiring exactly
  `vf` to be discarded would make the `[extension]` rule false, because that
  rule runs its subderivation with the enlarged frame `vf ++ S`. Nothing is
  lost: Wasm Logic assertions have a fixed stack length, which together with the
  arity checked at `BigStepN.labelBrZero` and `BigStepN.frameRet` pins the
  transferred values down exactly.
* The final abstract store `ρ'` is required to agree with `ρ` on every variable
  the code does not modify. Figure 17 leaves `ρ'` constrained only by
  reification, which is too weak twice over: a postcondition such as
  `[] | emp ∧ l₀ = x` of the `[set_local]` rule could be satisfied by re-reading
  the logical variable `x`, and, more seriously, the `[frame]` rule would be
  unprovable, since re-establishing the framed-off assertion under `ρ'` is
  exactly what its `fv(Hf) ∩ mv(e*) = ∅` side condition is for.

The index `n` bounds the height of the execution's derivation. It is what
`Triple.sound` recurses on, and it is discharged at the end by
`Execution.bigStep_iff_exists_height` to give `ValidBig`.

## The proof rules

Figures 6 to 11 of Watt et al. `Triple Γ P code Q` is the paper's
`Γ ⊢ {P} code {Q}`, with the context `Γ` carrying the module's functions, the
assumed function specifications, the label assertions and the return assertion.

Deviations from the paper, all recorded in `docs/projects/wasm-wasi.md`:

* The paper's `callcl` administrative instruction does not appear. Triples are
  over source instruction sequences only, and the `[function]` rule becomes
  `FuncRule`, a side condition of `ModuleSpecs` rather than a `Triple`
  constructor. Our `Execution.AdminInstr.invoke` takes a function *address*
  resolved through the store, whereas the paper's `callcl` takes the closure
  itself; `ReifiesFuncs` ties the two together.
* Typing side conditions that the paper gets for free from WebAssembly
  validation are explicit. The operand terms of each rule are typed — `Term.int`,
  `Term.i32`, `Term.float` — and `select` carries the equal-type premise that
  `Execution.PureStep.selectZero` requires.
* The `[consequence]` rule drops the paper's `n' ≤ n` stack-length side
  conditions on the label and return assertions. Figure 10 needs them because
  the hypotheses of Figure 17 include `reifies_lab(labs, L)` and
  `reifies_ret(ret, R)`, which pin each label assertion's stack length to the
  machine's label arity; `Valid` has no such conjunct, since `BigStepN` carries
  no `labs` or `ret` index, so the subderivation applies to the very same
  execution whatever the label assertions' stack lengths are.
* `Triple.empty` is added, for the empty instruction sequence. The paper needs
  it for `[seq]` to have a unit but does not list it.
* `[context]` is split into `Triple.context`, which enlarges the label list, and
  `Triple.contextRet`, which supplies a return assertion where the subderivation
  had none.
* Packed loads and stores have no rule, matching Figure 8, which covers only
  the full-width forms.
* The paper's `defined(cvtop, τ)` premise of `[cvtop]` is read as *every*
  permitted result of the conversion is the named one, not merely that the
  named one is permitted. `Execution.Numerics.convertRel` is nondeterministic
  on NaN payloads, so the weaker reading is unsound; see
  `convertRel_demote_nondeterministic` in `Silmaril.Proofs.Wasm.Logic.V1.Sound.Basic`
  for a machine-checked counterexample. `Triple.floatUnOp` and
  `Triple.floatBinOp` already read their premises this way.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.V1.Execution

/-- A function definition with its signature resolved. The source `V1.Func`
holds a `TypeIdx` into its module's type section; the logic needs the signature
itself, exactly as the paper's `func t* → t* local t* e*` does. -/
structure FuncDef where
  type : Silmaril.Wasm.V1.FuncType
  locals : List Silmaril.Wasm.V1.ValType
  body : Silmaril.Wasm.V1.Expr

/-- The local variables of the abstract store agree with the frame. -/
def ReifiesLocals (locals : List Value) (ρ : Sto) : Prop :=
  ∀ (i : Nat) (v : Value), locals[i]? = some v → ρ (.loc i) = v

/-- The global variables of the abstract store agree with the store, and the
module's global addresses are distinct. -/
structure ReifiesGlobals {H : Type*} (s : Store H) (md : ModuleInst) (ρ : Sto) : Prop where
  nodup : md.globals.Nodup
  agree : ∀ (i : Nat) (a : GlobalAddr) (g : GlobalInst), md.globals[i]? = some a → s.globals[a.value]? = some g → ρ (.glob i) = g.value

/-- The owned addresses agree with the linear memory, and the page-count
resource, when owned, agrees with the memory's size. -/
def ReifiesMem {H : Type*} (s : Store H) (md : ModuleInst) (h : AHeap) : Prop :=
  ∃ (a : MemAddr) (m : MemInst), md.memories[0]? = some a ∧ s.memories[a.value]? = some m ∧
    (∀ (i : Nat) (b : Memory.Byte), h.cells i = some b → m.data[i]? = some b) ∧
    (∀ n, h.size = some n → Memory.size m.data = n)

/-- The module's functions are the ones the context lists, and every call in it
stays inside the module: the paper's `∀i. F!i = funcs(s)!((faddrs inst)!i)`,
with encapsulation made explicit by requiring the callee's instance to be the
caller's. -/
def ReifiesFuncs {H : Type*} (F : List FuncDef) (s : Store H) (md : ModuleInst) : Prop :=
  F.length = md.funcs.length ∧
  ∀ (i : Nat) (d : FuncDef), F[i]? = some d → ∃ (a : FuncAddr) (fn : Silmaril.Wasm.V1.Func), md.funcs[i]? = some a ∧
    s.funcs[a.value]? = some (FuncInst.wasm d.type md fn) ∧
    fn.locals = d.locals ∧ fn.body = d.body

/-- The whole of Figure 16's reification, bundled. -/
structure Reifies {H : Type*} (F : List FuncDef) (s : Store H) (f : Frame) (ρ : Sto)
    (h : AHeap) : Prop where
  funcs : ReifiesFuncs F s f.module
  locals : ReifiesLocals f.locals ρ
  globals : ReifiesGlobals s f.module ρ
  mem : ReifiesMem s f.module h

end Silmaril.Wasm.Logic.V1

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.V1.Execution

variable {H : Type*}

/-- What an outcome has to satisfy, given the postcondition, the label
assertions and the return assertion. -/
def Satisfies (L : List Assert) (R : Option Assert) (Q : Assert) (ρ : Sto) (vf : List Value)
    (h : AHeap) (res : BigResult) : Prop :=
  match res with
  | .normal ws => ∃ ws', ws = vf ++ ws' ∧ Q ρ ws' h
  | .br l ws => ∃ P pre ws', L[l.toNat]? = some P ∧ ws = pre ++ ws' ∧ P ρ ws' h
  | .ret ws => ∃ R' pre ws', R = some R' ∧ ws = pre ++ ws' ∧ R' ρ ws' h
  | .trap => False

/-- The semantic Wasm Logic triple, for executions of derivation height at
most `n`. -/
def Valid (host : HostSemantics H) (n : Nat) (F : List FuncDef) (L : List Assert)
    (R : Option Assert) (P : Assert) (code : Silmaril.Wasm.V1.Expr) (Q : Assert) : Prop :=
  ∀ (s : Store H) (f : Frame) (ρ : Sto) (vs vf : List Value) (h hf : AHeap) (o : Outcome H),
    P ρ vs h → AHeap.Disj h hf → Reifies F s f ρ (h ∪ hf) →
    BigStepN host n s f (vf ++ vs) (expression code) o →
    ∃ h' ρ', AHeap.Disj h' hf ∧ Reifies F o.store o.frame ρ' (h' ∪ hf) ∧
      (∀ x, x ∉ Expr.modified code → ρ' x = ρ x) ∧
      Satisfies L R Q ρ' vf h' o.result

/-- The semantic triple against the unindexed big-step semantics. -/
def ValidBig (host : HostSemantics H) (F : List FuncDef) (L : List Assert)
    (R : Option Assert) (P : Assert) (code : Silmaril.Wasm.V1.Expr) (Q : Assert) : Prop :=
  ∀ (s : Store H) (f : Frame) (ρ : Sto) (vs vf : List Value) (h hf : AHeap) (o : Outcome H),
    P ρ vs h → AHeap.Disj h hf → Reifies F s f ρ (h ∪ hf) →
    BigStep host s f (vf ++ vs) (expression code) o →
    ∃ h' ρ', AHeap.Disj h' hf ∧ Reifies F o.store o.frame ρ' (h' ∪ hf) ∧
      (∀ x, x ∉ Expr.modified code → ρ' x = ρ x) ∧
      Satisfies L R Q ρ' vf h' o.result

theorem validBig_of_valid {host : HostSemantics H} {F L R P code Q}
    (h : ∀ n, Valid host n F L R P code Q) : ValidBig host F L R P code Q := by
  intro s f ρ vs vf hp hf o pre disj reify run
  obtain ⟨n, run⟩ := run.toHeight
  exact h n s f ρ vs vf hp hf o pre disj reify run

/-- The final store agrees with the initial one on logical variables. -/
theorem Sto.log_agree_of_modified {code : Silmaril.Wasm.V1.Expr} {ρ ρ' : Sto}
    (agree : ∀ x, x ∉ Expr.modified code → ρ' x = ρ x) (x : Var) (h : ¬ x.IsProgram) :
    ρ' x = ρ x := Sto.not_isProgram_of_agree agree x h

theorem Valid.mono {host : HostSemantics H} {n m F L R P code Q} (le : m ≤ n)
    (h : Valid host n F L R P code Q) : Valid host m F L R P code Q :=
  fun s f ρ vs vf hp hf o pre disj reify run =>
    h s f ρ vs vf hp hf o pre disj reify (run.mono le)

/-- A triple never holds of an execution that traps: this is the paper's
`res ≠ Trap` conjunct, here folded into `Satisfies`. -/
theorem Valid.not_trap {host : HostSemantics H} {n F L R P code Q}
    (h : Valid host n F L R P code Q) {s f ρ vs vf hp hf o} (pre : P ρ vs hp)
    (disj : AHeap.Disj hp hf) (reify : Reifies F s f ρ (hp ∪ hf))
    (run : BigStepN host n s f (vf ++ vs) (expression code) o) : o.result ≠ .trap := by
  obtain ⟨h', ρ', -, -, -, sat⟩ := h s f ρ vs vf hp hf o pre disj reify run
  intro eq
  rw [eq] at sat
  exact sat.elim

/-- Specifications assumed for the module's functions: the paper's `A`. -/
abbrev FuncSpecs := FuncIdx → Assert → Assert → Prop

/-- The semantic meaning of a function specification. -/
def ValidCall (host : HostSemantics H) (n : Nat) (F : List FuncDef) (i : FuncIdx)
    (P Q : Assert) : Prop :=
  Valid host n F [] none P [.call i] Q

def ValidSpecs (host : HostSemantics H) (n : Nat) (F : List FuncDef) (A : FuncSpecs) : Prop :=
  ∀ i P Q, A i P Q → ValidCall host n F i P Q

end Silmaril.Wasm.Logic.V1

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

/-- The paper's `Γ = (F, A, L, R)`. -/
structure Ctx where
  funcs : List FuncDef
  assume : FuncSpecs
  labels : List Assert
  ret : Option Assert

/-- The paper's `P; Γ`: push a label assertion. -/
def Ctx.push (Γ : Ctx) (P : Assert) : Ctx := { Γ with labels := P :: Γ.labels }

/-- The byte offset a memory access with this immediate reaches, as a term. -/
def memAddr (arg : Silmaril.Wasm.V1.MemArg) (a : Term (BitVec 32)) : Term Nat :=
  fun ρ => (a ρ).toNat + arg.offset.val

/-- `Γ ⊢ {P} code {Q}`. -/
inductive Triple : Ctx → Assert → Silmaril.Wasm.V1.Expr → Assert → Prop where
  -- Structural rules, Figure 10.
  | empty {Γ : Ctx} {P : Assert} : Triple Γ P [] P
  | seq {Γ : Ctx} {P Q R : Assert} {e₁ e₂ : Silmaril.Wasm.V1.Expr}
      (first : Triple Γ P e₁ Q) (second : Triple Γ Q e₂ R) : Triple Γ P (e₁ ++ e₂) R
  | consequence {F : List FuncDef} {A : FuncSpecs} {L L' : List Assert}
      {R R' : Option Assert} {P P' Q Q' : Assert} {e : Silmaril.Wasm.V1.Expr}
      (inner : Triple ⟨F, A, L', R'⟩ P' e Q')
      (pre : Assert.Entails P P') (post : Assert.Entails Q' Q)
      (labelLen : L.length = L'.length)
      (labels : ∀ (i : Nat) (P₁ P₁' : Assert), L[i]? = some P₁ → L'[i]? = some P₁' →
        Assert.Entails P₁' P₁)
      (return_ : ∀ R₁' : Assert, R' = some R₁' → ∃ R₁, R = some R₁ ∧ Assert.Entails R₁' R₁) :
      Triple ⟨F, A, L, R⟩ P e Q
  | frame {F : List FuncDef} {A : FuncSpecs} {L : List Assert} {R : Option Assert}
      {P Q : Assert} {e : Silmaril.Wasm.V1.Expr} (Hf : HAssert)
      (inner : Triple ⟨F, A, L, R⟩ P e Q) (indep : HAssert.Indep (Expr.modified e) Hf) :
      Triple ⟨F, A, L.map (fun P' => P'.frame Hf), R.map (fun R' => R'.frame Hf)⟩
        (P.frame Hf) e (Q.frame Hf)
  | exists_ {α : Type} {F : List FuncDef} {A : FuncSpecs} {L : List (α → Assert)}
      {R : Option (α → Assert)} {P Q : α → Assert} {e : Silmaril.Wasm.V1.Expr}
      (inner : ∀ a, Triple ⟨F, A, L.map (fun g => g a), R.map (fun g => g a)⟩ (P a) e (Q a)) :
      Triple ⟨F, A, L.map Assert.ex, R.map Assert.ex⟩ (Assert.ex P) e (Assert.ex Q)
  | extension {Γ : Ctx} {P Q : Assert} {e : Silmaril.Wasm.V1.Expr} (S : List (Term Value))
      (inner : Triple Γ P e Q)
      (indep : ∀ τ ∈ S, Term.Indep (Expr.modified e) τ) :
      Triple Γ (Assert.extend S P) e (Assert.extend S Q)
  | context {F : List FuncDef} {A : FuncSpecs} {L Lf : List Assert} {R : Option Assert}
      {P Q : Assert} {e : Silmaril.Wasm.V1.Expr} (inner : Triple ⟨F, A, L, R⟩ P e Q) :
      Triple ⟨F, A, L ++ Lf, R⟩ P e Q
  | contextRet {F : List FuncDef} {A : FuncSpecs} {L : List Assert} {R : Option Assert}
      {P Q : Assert} {e : Silmaril.Wasm.V1.Expr} (inner : Triple ⟨F, A, L, none⟩ P e Q) :
      Triple ⟨F, A, L, R⟩ P e Q
  -- Basic instructions, Figure 6.
  | const (Γ : Ctx) (v : Value) :
      Triple Γ (Assert.stack []) [constInstr v] (Assert.stack [Term.const v])
  | unreachable (Γ : Ctx) (Q : Assert) :
      Triple Γ (Assert.stackIf [] fun _ => False) [.unreachable] Q
  | nop (Γ : Ctx) : Triple Γ (Assert.stack []) [.nop] (Assert.stack [])
  | drop (Γ : Ctx) (τ : Term Value) : Triple Γ (Assert.stack [τ]) [.drop] (Assert.stack [])
  | select (Γ : Ctx) (τ₁ τ₂ : Term Value) (c : Term (BitVec 32))
      (sameType : ∀ ρ, (τ₁ ρ).type = (τ₂ ρ).type) :
      Triple Γ (Assert.stack [τ₁, τ₂, Term.i32 c]) [.select]
        (Assert.ex fun x : Value => Assert.stackIf [Term.const x] fun ρ =>
          (c ρ ≠ 0 → x = τ₁ ρ) ∧ (c ρ = 0 → x = τ₂ ρ))
  | intUnOp (Γ : Ctx) (t : IntType) (op : Silmaril.Wasm.V1.IntUnOp) (x : Term (BitVec t.width)) :
      Triple Γ (Assert.stack [Term.int t x]) [.intUnOp t op]
        (Assert.stack [Term.int t fun ρ => Numerics.intUnOp t op.toCore (x ρ)])
  | intBinOp (Γ : Ctx) (t : IntType) (op : IntBinOp) (x y z : Term (BitVec t.width)) :
      Triple Γ
        (Assert.stackIf [Term.int t x, Term.int t y] fun ρ =>
          Numerics.intBinOp t op (x ρ) (y ρ) = .ok (z ρ))
        [.intBinOp t op] (Assert.stack [Term.int t z])
  | intTestOp (Γ : Ctx) (t : IntType) (op : IntTestOp) (x : Term (BitVec t.width)) :
      Triple Γ (Assert.stack [Term.int t x]) [.intTestOp t op]
        (Assert.stack [Term.i32 fun ρ => Numerics.intTestOp t op (x ρ)])
  | intRelOp (Γ : Ctx) (t : IntType) (op : IntRelOp) (x y : Term (BitVec t.width)) :
      Triple Γ (Assert.stack [Term.int t x, Term.int t y]) [.intRelOp t op]
        (Assert.stack [Term.i32 fun ρ => Numerics.intRelOp t op (x ρ) (y ρ)])
  | floatUnOp (Γ : Ctx) (t : FloatType) (op : FloatUnOp) (x y : Term (BitVec t.width)) :
      Triple Γ
        (Assert.stackIf [Term.float t x] fun ρ =>
          ∀ z, Numerics.floatUnOpRel t op (x ρ) z → z = y ρ)
        [.floatUnOp t op] (Assert.stack [Term.float t y])
  | floatBinOp (Γ : Ctx) (t : FloatType) (op : FloatBinOp) (x y z : Term (BitVec t.width)) :
      Triple Γ
        (Assert.stackIf [Term.float t x, Term.float t y] fun ρ =>
          ∀ w, Numerics.floatBinOpRel t op (x ρ) (y ρ) w → w = z ρ)
        [.floatBinOp t op] (Assert.stack [Term.float t z])
  | floatRelOp (Γ : Ctx) (t : FloatType) (op : FloatRelOp) (x y : Term (BitVec t.width)) :
      Triple Γ (Assert.stack [Term.float t x, Term.float t y]) [.floatRelOp t op]
        (Assert.stack [Term.i32 fun ρ => Numerics.floatRelOp t op (x ρ) (y ρ)])
  | convert (Γ : Ctx) (op : Silmaril.Wasm.V1.ConvertOp) (x : Term (Numerics.NumValue op.toCore.source))
      (y : Term (Numerics.NumValue op.toCore.target)) :
      Triple Γ
        (Assert.stackIf [fun ρ => ⟨op.toCore.source, x ρ⟩] fun ρ =>
          (∀ y', Numerics.convertRel op.toCore (x ρ) (.ok y') → y' = y ρ) ∧
          ∀ e, ¬ Numerics.convertRel op.toCore (x ρ) (.error e))
        [.convert op] (Assert.stack [fun ρ => ⟨op.toCore.target, y ρ⟩])
  -- Variable management, Figure 7.
  | localGet (Γ : Ctx) (i : LocalIdx) :
      Triple Γ (Assert.stack []) [.localGet i] (Assert.stack [Term.local_ i.toNat])
  | localSet (Γ : Ctx) (i : LocalIdx) (v : Value) :
      Triple Γ (Assert.stack [Term.const v]) [.localSet i]
        (Assert.stackIf [] fun ρ => ρ (.loc i.toNat) = v)
  | localTee (Γ : Ctx) (i : LocalIdx) (v : Value) :
      Triple Γ (Assert.stack [Term.const v]) [.localTee i]
        (Assert.stackIf [Term.const v] fun ρ => ρ (.loc i.toNat) = v)
  | globalGet (Γ : Ctx) (i : GlobalIdx) :
      Triple Γ (Assert.stack []) [.globalGet i] (Assert.stack [Term.global i.toNat])
  | globalSet (Γ : Ctx) (i : GlobalIdx) (v : Value) :
      Triple Γ (Assert.stack [Term.const v]) [.globalSet i]
        (Assert.stackIf [] fun ρ => ρ (.glob i.toNat) = v)
  -- Memory management, Figure 8.
  | intLoad (Γ : Ctx) (t : IntType) (arg : Silmaril.Wasm.V1.MemArg) (a : Term (BitVec 32))
      (v : Term (BitVec t.width)) :
      Triple Γ (Assert.mk [Term.i32 a] (HAssert.cellNum (.int t) (memAddr arg a) v))
        [.intLoad t none arg]
        (Assert.mk [Term.int t v] (HAssert.cellNum (.int t) (memAddr arg a) v))
  | floatLoad (Γ : Ctx) (t : FloatType) (arg : Silmaril.Wasm.V1.MemArg) (a : Term (BitVec 32))
      (v : Term (BitVec t.width)) :
      Triple Γ (Assert.mk [Term.i32 a] (HAssert.cellNum (.float t) (memAddr arg a) v))
        [.floatLoad t arg]
        (Assert.mk [Term.float t v] (HAssert.cellNum (.float t) (memAddr arg a) v))
  | intStore (Γ : Ctx) (t : IntType) (arg : Silmaril.Wasm.V1.MemArg) (a : Term (BitVec 32))
      (v : Term (BitVec t.width)) :
      Triple Γ
        (Assert.mk [Term.i32 a, Term.int t v] (HAssert.cellNumAny (.int t) (memAddr arg a)))
        [.intStore t none arg]
        (Assert.mk [] (HAssert.cellNum (.int t) (memAddr arg a) v))
  | floatStore (Γ : Ctx) (t : FloatType) (arg : Silmaril.Wasm.V1.MemArg) (a : Term (BitVec 32))
      (v : Term (BitVec t.width)) :
      Triple Γ
        (Assert.mk [Term.i32 a, Term.float t v] (HAssert.cellNumAny (.float t) (memAddr arg a)))
        [.floatStore t arg]
        (Assert.mk [] (HAssert.cellNum (.float t) (memAddr arg a) v))
  | memorySize (Γ : Ctx) (p : Term Nat) :
      Triple Γ (Assert.mk [] (HAssert.size p)) [.memorySize]
        (Assert.mk [Term.i32 fun ρ => BitVec.ofNat 32 (p ρ)] (HAssert.size p))
  | memoryGrow (Γ : Ctx) (d : Term (BitVec 32)) (p : Term Nat) :
      Triple Γ (Assert.mk [Term.i32 d] (HAssert.size p)) [.memoryGrow]
        (Assert.ex fun r : BitVec 32 => Assert.mk [Term.i32 fun _ => r]
          (HAssert.or
            (HAssert.and
              (HAssert.star
                (HAssert.iter (fun ρ => p ρ * Memory.pageSize)
                  (fun ρ => (p ρ + (d ρ).toNat) * Memory.pageSize)
                  (fun i => HAssert.cell (fun _ => i) (fun _ => 0)))
                (HAssert.size fun ρ => p ρ + (d ρ).toNat))
              (HAssert.pure fun ρ =>
                r = BitVec.ofNat 32 (p ρ) ∧ p ρ + (d ρ).toNat ≤ Memory.maxPages))
            (HAssert.and (HAssert.size p) (HAssert.pure fun _ => r = -1))))
  -- Control flow, Figure 9.
  | br {Γ : Ctx} (l : LabelIdx) (P Q : Assert) (target : Γ.labels[l.toNat]? = some P) :
      Triple Γ P [.br l] Q
  | return_ {Γ : Ctx} (R Q : Assert) (target : Γ.ret = some R) : Triple Γ R [.return_] Q
  | block {Γ : Ctx} {P Q : Assert} (bt : Silmaril.Wasm.V1.BlockType) (body : Silmaril.Wasm.V1.Expr)
      (pre : Assert.StackLen P 0) (post : Assert.StackLen Q bt.toList.length)
      (inner : Triple (Γ.push Q) P body Q) : Triple Γ P [.block bt body] Q
  | loop {Γ : Ctx} {P Q : Assert} (bt : Silmaril.Wasm.V1.BlockType) (body : Silmaril.Wasm.V1.Expr)
      (pre : Assert.StackLen P 0) (post : Assert.StackLen Q bt.toList.length)
      (inner : Triple (Γ.push P) P body Q) : Triple Γ P [.loop bt body] Q
  | if_ {Γ : Ctx} {Q : Assert} (bt : Silmaril.Wasm.V1.BlockType) (left right : Silmaril.Wasm.V1.Expr)
      (S : List (Term Value)) (Hp : HAssert) (c : Term (BitVec 32))
      (hthen : Triple Γ (Assert.mk S (HAssert.and Hp (HAssert.pure fun ρ => c ρ ≠ 0)))
        [.block bt left] Q)
      (helse : Triple Γ (Assert.mk S (HAssert.and Hp (HAssert.pure fun ρ => c ρ = 0)))
        [.block bt right] Q) :
      Triple Γ (Assert.mk (S ++ [Term.i32 c]) Hp) [.if_ bt left right] Q
  | brIf {Γ : Ctx} {Q : Assert} (l : LabelIdx) (S : List (Term Value)) (Hp : HAssert)
      (c : Term (BitVec 32))
      (taken : Triple Γ (Assert.mk S (HAssert.and Hp (HAssert.pure fun ρ => c ρ ≠ 0)))
        [.br l] Q) :
      Triple Γ (Assert.mk (S ++ [Term.i32 c]) Hp) [.brIf l]
        (Assert.mk S (HAssert.and Hp (HAssert.pure fun ρ => c ρ = 0)))
  | brTable {Γ : Ctx} {Q : Assert} (ls : List LabelIdx) (dflt : LabelIdx)
      (S : List (Term Value)) (Hp : HAssert) (c : Term (BitVec 32))
      (cases : ∀ (k : Nat) (l : LabelIdx), ls[k]? = some l →
        Triple Γ (Assert.mk S (HAssert.and Hp (HAssert.pure fun ρ => (c ρ).toNat = k)))
          [.br l] Q)
      (dfltCase : Triple Γ
        (Assert.mk S (HAssert.and Hp (HAssert.pure fun ρ => ls.length ≤ (c ρ).toNat)))
        [.br dflt] Q) :
      Triple Γ (Assert.mk (S ++ [Term.i32 c]) Hp) [.brTable ls dflt] Q
  -- Function calls, Figure 11.
  | call {Γ : Ctx} (i : FuncIdx) (P Q : Assert) (assumed : Γ.assume i P Q)
      (bound : i.toNat < Γ.funcs.length) : Triple Γ P [.call i] Q

/-- The precondition the body of a function is verified from: the arguments
have moved from the stack into the leading local variables, the declared locals
are zero, and the operand stack is empty. -/
def enterFunc (d : FuncDef) (P : Assert) : Assert := fun ρ vs h =>
  vs = [] ∧ ∃ args : List Value, args.length = d.type.params.length ∧ P ρ args h ∧
    ReifiesLocals (args ++ d.locals.map Value.zero) ρ

/-- The set of local variables, which function pre- and postconditions may not
mention: the paper's `∀i. lᵢ ∉ fv(Sₙ) ∪ fv(H) ∪ fv(Qₘ)`. -/
def localVars : Set Var := {x | ∃ j, x = Var.loc j}

/-- The premise of the paper's `[function]` rule. -/
structure FuncRule (F : List FuncDef) (A : FuncSpecs) (d : FuncDef) (P Q : Assert) : Prop where
  pre : Assert.StackLen P d.type.params.length
  post : Assert.StackLen Q d.type.results.length
  results : d.type.results.length ≤ 1
  preLocals : Assert.Indep localVars P
  postLocals : Assert.Indep localVars Q
  body : Triple ⟨F, A, [Q], some Q⟩ (enterFunc d P) d.body Q

/-- The paper's `[module]` rule: every assumed specification is established by
the corresponding function body, assuming all of them. -/
def ModuleSpecs (F : List FuncDef) (specs : FuncSpecs) : Prop :=
  ∀ i P Q, specs i P Q → ∃ d, F[i.toNat]? = some d ∧ FuncRule F specs d P Q

end Silmaril.Wasm.Logic.V1
