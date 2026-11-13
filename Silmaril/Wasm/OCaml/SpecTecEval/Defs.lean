module

public import Silmaril.Raw.Wasm.OCaml.SpecTecPin.Gen.Program
public import Silmaril.Raw.Wasm.OCaml.SpecTecMain.Gen.Program
public import Silmaril.ML.OCaml.Override.Defs
public import Silmaril.ML.OCaml.Interp.Defs
public import Silmaril.Wasm.SpecTec.Defs

/-!
# SpecTec's IL interpreter, imported from its OCaml source

The programs of `il/eval.ml` at the two pins, imported by an OCaml-to-Lean import tool from OCaml
5.4.1's typed trees (`specs/ml/spectec-{pin,main}`), linked with Lean models of the units
that are not imported:

* `Z`: Zarith 1.14 with its real field layout, on `Int` (`Override.zarithUnit`);
* `Stdlib__Printexc`: `register_printer` does nothing (`Override.printexcUnit`); it is the
  only field used at link time;
* `Q`, `Stdlib__Printf`, `CamlinternalFormat`: stuck placeholders (`Override.stubUnit`).
  `il/eval.ml` reaches them only from its debug-logging closures and from rational
  arithmetic, so a run that touches them is stuck, never wrong.

The rest of this file builds IL expressions as OCaml values, following
`spectec/src/il/ast.ml` and `util/source.ml` at the pin:

* `exp = (exp', typ) note_phrase = {at : region; it : exp'; mutable note : typ}`: since
  `note` is mutable, an expression is a store cell with fields `[at, it, note]`;
* `exp'` constructors have arguments, so they are blocks: `NumE` has tag 2, `ListE` 16,
  `SliceE` 22 (the order of `ast.ml`);
* `` `Nat n `` is the pair `(hash, n)`, with `hash = 3900609` (`Btype.hash_variant "Nat"`,
  as the dump records it), and a small `Z.t` is a native `int`.

Notes are irrelevant to `reduce_exp` on these expressions; they are `()` here.
-/

@[expose] public section
namespace Silmaril.Wasm.OCaml.SpecTecEval

open Silmaril.ML.OCaml

/-- The external units, in the order they are linked before the imported ones. -/
def externals : Program :=
  [Override.zarithUnit, Override.stubUnit "Q" 100, Override.printexcUnit,
   Override.stubUnit "Stdlib__Printf" 100, Override.stubUnit "CamlinternalFormat" 300]

/-- `il/eval.ml` and what it reaches, at `WebAssembly/spec@608711107b`. -/
def pinProgram : Program := externals ++ SpecTecPin.Gen.program

/-- `il/eval.ml` and what it reaches, at `WebAssembly/spec@e7a9df7cd` (after the upstream
fix `f4f22691f` of the slice bound). -/
def mainProgram : Program := externals ++ SpecTecMain.Gen.program

/-- Enough fuel for linking and for the runs below; `interp_mono` makes the exact
amount irrelevant. -/
def fuel : Nat := 1000000

/-- The store after linking (initialising every unit, in order). -/
def link (p : Program) : Option Store :=
  match initProg .rtl fuel p with
  | .ok (.ret _) st => some st
  | _ => none

/-! ## IL expressions as OCaml values -/

/-- `Source.no_pos = {file = ""; line = 0; column = 0}`. -/
def noPos : Value := .block 0 [.str [], .ofInt 0, .ofInt 0]

/-- `Source.no_region`. -/
def noRegion : Value := .block 0 [noPos, noPos]

/-- The polymorphic-variant hash of `` `Nat ``. -/
def natHash : Nat := 3900609

/-- `NumE (`Nat n)`. -/
def numE (n : Nat) : Value := .block 2 [.block 0 [.ofInt natHash, .ofInt n]]

/-- `ListE es`. -/
def listE (es : List Value) : Value := .block 16 [Value.ofList es]

/-- `SliceE (e1, e2, e3)`. -/
def sliceE (e1 e2 e3 : Value) : Value := .block 22 [e1, e2, e3]

/-- Allocate the expression `{at = no_region; it; note = ()}`. -/
def mkExp (it : Value) (st : Store) : Value × Store :=
  let (l, st) := st.alloc (.fields [noRegion, it, .unit])
  (.loc l, st)

/-- Allocate a list of number expressions. -/
def mkNums : List Nat → Store → List Value × Store
  | [], st => ([], st)
  | n :: ns, st =>
    let (v, st) := mkExp (numE n) st
    let (vs, st) := mkNums ns st
    (v :: vs, st)

/-- `Il.Env.empty`: a record of five empty maps. (`Env.empty` itself is shaken away;
`reduce_exp` does not read the environment on the expressions used here.) -/
def emptyEnv : Value := .block 0 (List.replicate 5 (.cconst 0))

/-- Run `Il.Eval.reduce_exp env e` (the exported `reduce_exp`, `= reduce_exp false`,
field 3 of `Il__Eval`) on the expression `mk` allocates, in the store `p` links to. -/
def runReduce (p : Program) (mk : Store → Value × Store) : Res :=
  match link p with
  | none => .stuck "link"
  | some st =>
    match st.globals.lookup "Il__Eval" with
    | some (.mod fs) =>
      let (e, st) := mk st
      interp .rtl fuel st [] (.apply (fs.getD 3 default) [emptyEnv, e])
    | _ => .stuck "Il__Eval"

/-- `reduce_exp` on `es[i : n]`, where `es` is a list of natural-number literals. -/
def runSlice (p : Program) (es : List Nat) (i n : Nat) : Res :=
  runReduce p fun st =>
    let (vs, st) := mkNums es st
    let (e1, st) := mkExp (listE vs) st
    let (e2, st) := mkExp (numE i) st
    let (e3, st) := mkExp (numE n) st
    mkExp (sliceE e1 e2 e3) st

/-! ## Arithmetic and comparisons -/

/-- The polymorphic-variant hash of `` `Int ``. -/
def intHash : Nat := 3654863

/-- A numeral of `Xl.Num.num`: `` `Nat n `` or `` `Int i `` (both carry a `Z.t`, which is
a native `int` when small). -/
inductive Lit where
  | nat (n : Nat)
  | int (i : Int)
  deriving DecidableEq, Repr

def Lit.value : Lit → Value
  | .nat n => .block 0 [.ofInt natHash, .ofInt n]
  | .int i => .block 0 [.ofInt intHash, .ofInt i]

/-- The hashes of `Xl.Num`'s binary and comparison operators (the dump's `pvariant` nodes):
`` `AddOp ``, `` `SubOp ``, `` `MulOp ``, `` `DivOp ``, `` `ModOp ``, `` `PowOp ``. -/
def binHash : Nat → Int
  | 0 => 795947394 | 1 => 400735905 | 2 => 595778085 | 3 => -318723918 | 4 => 528842851
  | _ => -641226567

/-- `` `EqOp ``, `` `NeOp ``, `` `LtOp ``, `` `GtOp ``, `` `LeOp ``, `` `GeOp ``. -/
def cmpHash : Nat → Int
  | 0 => 770817229 | 1 => 870026584 | 2 => 848593385 | 3 => 793145550 | 4 => 847847450
  | _ => 792399615

/-- `` `NatT `` and `` `IntT ``, the operator types. -/
def natTHash : Int := 869835891
def intTHash : Int := 815034533

def Lit.optyp : Lit → Value
  | .nat _ => .ofInt natTHash
  | .int _ => .ofInt intTHash

/-- `reduce_exp` on `BinE (op, ot, NumE a, NumE b)`, with `op` numbered as in `binHash`. -/
def runBin (p : Program) (op : Nat) (a b : Lit) : Res :=
  runReduce p fun st =>
    let (e1, st) := mkExp (.block 2 [a.value]) st
    let (e2, st) := mkExp (.block 2 [b.value]) st
    mkExp (.block 5 [.ofInt (binHash op), a.optyp, e1, e2]) st

/-- `reduce_exp` on `CmpE (op, ot, NumE a, NumE b)`, with `op` numbered as in `cmpHash`. -/
def runCmp (p : Program) (op : Nat) (a b : Lit) : Res :=
  runReduce p fun st =>
    let (e1, st) := mkExp (.block 2 [a.value]) st
    let (e2, st) := mkExp (.block 2 [b.value]) st
    mkExp (.block 6 [.ofInt (cmpHash op), a.optyp, e1, e2]) st

/-! ## Reading results back -/

/-- The `it` field of an expression. -/
def itOf (st : Store) : Value → Option Value
  | .loc l => match st.get? l with
    | some (.fields [_, it, _]) => some it
    | _ => none
  | _ => none

/-- The natural number a `NumE (`Nat n)` expression denotes. -/
def readNum (st : Store) (e : Value) : Option Nat :=
  match itOf st e with
  | some (.block 2 [.block 0 [.int h, .int n]]) =>
    if h.toNat = natHash ∧ 0 ≤ n.toInt then some n.toNat else none
  | _ => none

/-- The elements of an OCaml list. -/
def listElems : Value → Nat → Option (List Value)
  | .cconst 0, _ => some []
  | .block 0 [x, xs], k + 1 => (listElems xs k).map (x :: ·)
  | _, _ => none

/-- What `reduce_exp` returned on a slice: `Ok (ListE es')` with the literals of `es'`,
`Error e'` with `e'.it` a `SliceE`, or anything else. -/
inductive SliceOut where
  | ok (ns : List Nat)
  | errorSlice
  | other
  deriving DecidableEq, Repr

def sliceOut : Res → SliceOut
  | .ok (.ret (.block 0 [e])) st => match itOf st e with
    | some (.block 16 [l]) => match listElems l (st.cells.length + 1) with
      | some vs => match vs.mapM (readNum st) with
        | some ns => .ok ns
        | none => .other
      | none => .other
    | _ => .other
  | .ok (.ret (.block 1 [e])) st => match itOf st e with
    | some (.block 22 [_, _, _]) => .errorSlice
    | _ => .other
  | _ => .other

/-- What `reduce_exp` returned on an operator: `Ok (NumE l)`, `Ok (BoolE b)`, `Ok e'` with
`e'.it` still the operator node (tag `t`: not reduced), or anything else. -/
inductive OpOut where
  | num (l : Lit)
  | bool (b : Bool)
  | unreduced (tag : Nat)
  | other
  deriving DecidableEq, Repr

/-- A numeral, with its `Z.t` small (a native `int`) or large (`Value.z`). -/
def readLit : Value → Option Lit
  | .block 0 [.int h, v] => match zOf? v with
    | some n =>
      if h.toInt = natHash ∧ 0 ≤ n then some (.nat n.toNat)
      else if h.toInt = intHash then some (.int n) else none
    | none => none
  | _ => none

def opOut : Res → OpOut
  | .ok (.ret (.block 0 [e])) st => match itOf st e with
    | some (.block 2 [l]) => match readLit l with
      | some l => .num l
      | none => .other
    | some (.block 1 [b]) => match b.toBool? with
      | some b => .bool b
      | none => .other
    | some (.block t _) => .unreduced t
    | _ => .other
  | _ => .other

/-- The constructor tags of `reduce_exp`'s answer: `Ok` (0) or `Error` (1), and the tag of
its expression's `it` (`ListE` 16, `SliceE` 22, …). It does not look at anything else, so
it reduces in the kernel when the list elements are symbolic. -/
def answerTags : Res → Option (Nat × Nat)
  | .ok (.ret (.block t [e])) st => match itOf st e with
    | some (.block u _) => some (t, u)
    | _ => none
  | _ => none

/-- The `it` fields of the elements of an `Ok (ListE es')` answer. -/
def answerElems : Res → Option (List Value)
  | .ok (.ret (.block 0 [e])) st => match itOf st e with
    | some (.block 16 [l]) => (listElems l (st.cells.length + 1)).bind fun vs => vs.mapM (itOf st)
    | _ => none
  | _ => none

/-! ## The Lean transcriptions they are compared with -/

/-- The `Sem.Value` of a natural-number literal. -/
def natV (n : Nat) : Silmaril.SpecTec.Sem.Value := .num (.natN n)

/-- The natural number a `Sem.Value` is, if it is one. -/
def natOf? : Silmaril.SpecTec.Sem.Value → Option Nat
  | .num (.natN n) => some n
  | _ => none

/-- Does `reduce_exp`'s answer on a slice agree with a slice function's? `Ok (ListE es')`
must be the slice, and `Error (SliceE …)` (no reduction) must be where the slice is
undefined. -/
def agreesSlice (f : Option Silmaril.SpecTec.Sem.Value) (o : SliceOut) : Bool :=
  match o, f with
  | .ok ns, some (.list ws) => ws.mapM natOf? == some ns
  | .errorSlice, none => true
  | _, _ => false

/-- The slice test cases `(es, i, n)`: every boundary case `i + n = |es|` for `|es|` in
`{0, 1, 3}`, and cases on either side. -/
def sliceCases : List (List Nat × Nat × Nat) :=
  [([], 0, 0), ([], 0, 1), ([7], 0, 0), ([7], 0, 1), ([7], 1, 0), ([7], 0, 2),
   ([7, 8, 9], 0, 2), ([7, 8, 9], 1, 1), ([7, 8, 9], 1, 2), ([7, 8, 9], 0, 3),
   ([7, 8, 9], 3, 0), ([7, 8, 9], 2, 2)]

def Lit.num : Lit → Silmaril.SpecTec.IL.Num
  | .nat n => .natN n
  | .int i => .intN i

def Lit.numTyp : Lit → Silmaril.SpecTec.IL.NumTyp
  | .nat _ => .natT
  | .int _ => .intT

/-- The binary operators in the order of `binHash`. -/
def binOp : Nat → Silmaril.SpecTec.IL.BinOp
  | 0 => .addOp | 1 => .subOp | 2 => .mulOp | 3 => .divOp | 4 => .modOp | _ => .powOp

/-- The comparison operators in the order of `cmpHash`. -/
def cmpOp : Nat → Silmaril.SpecTec.IL.CmpOp
  | 0 => .eqOp | 1 => .neOp | 2 => .ltOp | 3 => .gtOp | 4 => .leOp | _ => .geOp

/-- `Sem.evalExp` (Silmaril's transcription of `eval.ml`) on `a op b`. -/
def semBin (op : Nat) (a b : Lit) : Silmaril.SpecTec.Sem.Res Silmaril.SpecTec.Sem.Value :=
  Silmaril.SpecTec.Sem.evalExp 3 default default (.binE (binOp op) (.numT a.numTyp) (.numE a.num) (.numE b.num))

def semCmp (op : Nat) (a b : Lit) : Silmaril.SpecTec.Sem.Res Silmaril.SpecTec.Sem.Value :=
  Silmaril.SpecTec.Sem.evalExp 3 default default (.cmpE (cmpOp op) (.numT a.numTyp) (.numE a.num) (.numE b.num))

/-- Agreement on an operator node with tag `tag` (`BinE` 5, `CmpE` 6): a value of the
transcription is the literal (or boolean) `reduce_exp` reduces to, and no value means
`reduce_exp` leaves the node unreduced. -/
def agreesOp (tag : Nat) (r : Silmaril.SpecTec.Sem.Res Silmaril.SpecTec.Sem.Value) (o : OpOut) : Bool :=
  match r, o with
  | .ok (.num (.natN m)), .num (.nat n) => m == n
  | .ok (.num (.intN m)), .num (.int n) => m == n
  | .ok (.bool b), .bool c => b == c
  | .error _, .unreduced t => t == tag
  | _, _ => false

/-- Operand pairs for the arithmetic test: small, equal, zero, a sum and a product that
leave the 63-bit range (so `Z.t` becomes a large integer), and signed operands. -/
def opCases : List (Lit × Lit) :=
  [(.nat 12, .nat 5), (.nat 5, .nat 12), (.nat 12, .nat 0), (.nat 4611686018427387903, .nat 3),
   (.int (-12), .int 5), (.int 7, .int (-2))]

end Silmaril.Wasm.OCaml.SpecTecEval
