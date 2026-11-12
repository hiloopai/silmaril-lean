module

public import Silmaril.Wasm.SingleThreaded.Locality

@[expose] public section

/-!
# Function reachability over Core 3.0 stores

The invariant behind the automated verifier of `Silmaril.Wasm.Verify.Check`. Everything is stated
over a set `G : Nat → Prop` of function addresses (the functions that may be called) and the
function-address list `fs` of the module instance (`ModuleInst.funcs`).

* `instrCallees i`: the function indices that a source instruction names in `call`,
  `return_call` and `ref.func`, recursively through the bodies of `block`, `loop`, `if` and
  `try_table` (`exprCallees` for instruction lists). Structural, so it reduces in the kernel.
* `InstrIn G fs i`: every function index named by `i` resolves (through `fs`) into `G`.
* `codePlains code`: the source instructions of administrative code, including those inside
  `label`, `handler` and `frame` bodies and label continuations.
* `refFuncs r`: the function addresses in a reference (through `extern`); `RefIn G r`.
* `StoreIn G s`: every reference held by the store (globals, tables, element segments, struct,
  array and exception fields) is in `G`.
* `FrameIn G fs fr`: the frame's module has function list `fs` (or none at all, the frame of
  `$invoke`), and its locals hold references into `G`.
* `CodeIn G fs Pl code`: every reference value in the code is in `G`, every frame in it is
  `FrameIn`, every source instruction is acceptable for `Pl` (`PlOK`: it names no function or
  satisfies `Pl`; for reachability `Pl = InstrIn G fs`).
* `CfgIn G fs Pl c`: the three together, for a configuration.
* `FuncsClosed G fs Pl funcs`: every Wasm function in `G` belongs to the module instance with
  function list `fs`, and its body is acceptable for `Pl`.
* `PlainOK G Bad fs Pl`: what the invariant needs of `Pl` (closure under structured bodies;
  `call` targets in `G` or `Bad`, `return_call`/`ref.func` targets in `G`).
* `Avoids G funcs i`: no function in `G` is the host function `.host i` (import `i`).

The preservation theorem (`Silmaril.Proofs.Wasm.Verify.Reach`) shows that `CfgIn G fs Pl` is
preserved by every Core 3.0 step rule (`Step P host`, every profile `P`), for hosts that return
the store unchanged with references into `G` (`HostIn`), the empty host in particular, except
for one step: a `call` of a function in `Bad`, which leaves the configuration at that call.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Verify

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

/-! ## Function indices named by instructions -/

mutual

/-- The function indices named by `call`, `return_call` and `ref.func` in an instruction,
including nested bodies. -/
def instrCallees : Instr → List Nat
  | .call x => [x.toNat]
  | .returnCall x => [x.toNat]
  | .refFunc x => [x.toNat]
  | .block _ b => exprCallees b
  | .loop _ b => exprCallees b
  | .tryTable _ _ b => exprCallees b
  | .if_ _ b₁ b₂ => exprCallees b₁ ++ exprCallees b₂
  | _ => []

/-- The function indices named in an instruction sequence. -/
def exprCallees : List Instr → List Nat
  | [] => []
  | i :: is => instrCallees i ++ exprCallees is

end

/-- Every function index named by `i` resolves, through the function list `fs`, into `G`. -/
def InstrIn (G : Nat → Prop) (fs : List Nat) (i : Instr) : Prop :=
  ∀ x ∈ instrCallees i, ∀ a, fs[x]? = some a → G a

/-! ## Source instructions of administrative code -/

/-- The source instructions of administrative code, including nested bodies and label
continuations. -/
def codePlains : List Admin → List Instr
  | [] => []
  | .plain i :: rest => i :: codePlains rest
  | .label _ cont body :: rest => cont ++ codePlains body ++ codePlains rest
  | .handler _ _ body :: rest => codePlains body ++ codePlains rest
  | .frame _ _ body :: rest => codePlains body ++ codePlains rest
  | _ :: rest => codePlains rest

/-! ## References -/

/-- The function addresses in a reference (through `extern` wrappers). -/
def refFuncs : Ref → List Nat
  | .func a => [a]
  | .extern r => refFuncs r
  | _ => []

/-- Every function address in `r` is in `G`. -/
def RefIn (G : Nat → Prop) (r : Ref) : Prop := ∀ a ∈ refFuncs r, G a

/-! ## The invariant -/

variable {H : Type}

/-- Every reference held by the store is in `G`. -/
structure StoreIn (G : Nat → Prop) (s : Store H) : Prop where
  globals : ∀ g ∈ s.globals, ∀ r, g.value = .ref r → RefIn G r
  tables : ∀ t ∈ s.tables, ∀ r ∈ t.refs, RefIn G r
  elems : ∀ e ∈ s.elems, ∀ r ∈ e.refs, RefIn G r
  structs : ∀ si ∈ s.structs, ∀ r, FieldVal.val (.ref r) ∈ si.fields → RefIn G r
  arrays : ∀ ai ∈ s.arrays, ∀ r, FieldVal.val (.ref r) ∈ ai.fields → RefIn G r
  exns : ∀ e ∈ s.exns, ∀ r, Val.ref r ∈ e.fields → RefIn G r

/-- A frame of the module with function list `fs` (or of no module), whose locals hold
references into `G`. -/
def FrameIn (G : Nat → Prop) (fs : List Nat) (fr : Frame) : Prop :=
  (fr.module.funcs = fs ∨ fr.module.funcs = []) ∧ ∀ r, some (Val.ref r) ∈ fr.locals → RefIn G r

/-- A source instruction is acceptable for `Pl`: it names no function, or satisfies `Pl`. -/
def PlOK (Pl : Instr → Prop) (i : Instr) : Prop := instrCallees i = [] ∨ Pl i

/-- Administrative code whose references and frames stay in `G` and whose source
instructions are acceptable for `Pl` (for the reachability analysis, `Pl = InstrIn G fs`). -/
def CodeIn (G : Nat → Prop) (fs : List Nat) (Pl : Instr → Prop) (code : List Admin) : Prop :=
  (∀ r ∈ codeRefs code, RefIn G r) ∧ (∀ fr ∈ codeFrames code, FrameIn G fs fr) ∧
    ∀ i ∈ codePlains code, PlOK Pl i

/-- **The reachability invariant** of a configuration. -/
def CfgIn (G : Nat → Prop) (fs : List Nat) (Pl : Instr → Prop) (c : Config H) : Prop :=
  StoreIn G c.store ∧ FrameIn G fs c.frame ∧ CodeIn G fs Pl c.code

/-- Every Wasm function in `G` is a function of the module instance with function list `fs`,
and its body is acceptable for `Pl`. -/
def FuncsClosed (G : Nat → Prop) (fs : List Nat) (Pl : Instr → Prop) (funcs : List (FuncInst H)) :
    Prop :=
  ∀ a fi code, G a → funcs[a]? = some fi → fi.code = .wasm code →
    fi.module.funcs = fs ∧ ∀ i ∈ code.body, PlOK Pl i

/-- What the invariant needs of the source-instruction predicate `Pl`: it is inherited by the
bodies of structured instructions, and the functions named by `return_call` and `ref.func` are
in `G`, those named by `call` in `G` or in `Bad` (the guarded calls of the assertion
analysis; `Bad` is empty for the reachability analysis). -/
structure PlainOK (G Bad : Nat → Prop) (fs : List Nat) (Pl : Instr → Prop) : Prop where
  block : ∀ bt b, Pl (.block bt b) → ∀ i ∈ b, PlOK Pl i
  loop : ∀ bt b, Pl (.loop bt b) → ∀ i ∈ b, PlOK Pl i
  tryTable : ∀ bt cs b, Pl (.tryTable bt cs b) → ∀ i ∈ b, PlOK Pl i
  ifLeft : ∀ bt b₁ b₂, Pl (.if_ bt b₁ b₂) → PlOK Pl (.block bt b₁)
  ifRight : ∀ bt b₁ b₂, Pl (.if_ bt b₁ b₂) → PlOK Pl (.block bt b₂)
  call : ∀ (x : FuncIdx) a, Pl (.call x) → fs[x.toNat]? = some a → G a ∨ Bad a
  returnCall : ∀ (x : FuncIdx) a, Pl (.returnCall x) → fs[x.toNat]? = some a → G a
  refFunc : ∀ (x : FuncIdx) a, Pl (.refFunc x) → fs[x.toNat]? = some a → G a

/-- A step that performs a `call` of a function in `Bad` (a guarded call of the assertion
analysis): the code is `E.fill [call x]` and becomes `E.fill [ref.func a, call_ref]`. -/
def BadStep (Bad : Nat → Prop) (fs : List Nat) (c c' : Config H) : Prop :=
  ∃ (E : SingleThreaded.Ctx) (x : FuncIdx) (a : Nat) (d : Validation.DefType),
    c.code = E.fill [.plain (.call x)] ∧
    c' = ⟨c.store, c.frame, E.fill [.ref (.func a), .callRefType d]⟩ ∧
    fs[x.toNat]? = some a ∧ Bad a

/-- No function in `G` is the host function `.host i`. -/
def Avoids (G : Nat → Prop) (funcs : List (FuncInst Nat)) (i : Nat) : Prop :=
  ∀ a fi, G a → funcs[a]? = some fi → fi.code ≠ .host i

/-- A host relation that returns the store unchanged, with results whose references are in
`G` (the empty host, and the hosts `hostOf ts K` of scalar environments). -/
def HostIn (G : Nat → Prop) (host : HostSemantics H) : Prop :=
  ∀ h s vs s' r, host h s vs (.returned s' r) → s' = s ∧ ∀ x ∈ codeRefs r.toAdmin, RefIn G x

end Silmaril.Wasm.Verify
