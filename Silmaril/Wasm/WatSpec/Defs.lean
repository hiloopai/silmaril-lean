module

public import Silmaril.Wasm.Wat
public import Silmaril.Wasm.Logic.VC.Defs
public import Silmaril.Wasm.Logic.VCTotal.Defs
public import Silmaril.Wasm.Logic.Memory.Defs
public import Silmaril.Wasm.Logic.Exec.Defs
public import Silmaril.Wasm.Verify.FnSpec.Defs
public meta import Silmaril.Wasm.Wat.CoreModules
public meta import Silmaril.Wasm.Wat.CoreInstructions
public meta import Silmaril.Wasm.Wat.Lexer

/-!
# Annotated WAT: functions with pre/postconditions and loop invariants

`wat_spec! "…"` reads **one WAT function with annotations** and elaborates to an `Annotated`:
the plain module `(module (func …))` (built by silmaril-lean's `wat3!` frontend from the text
with the annotations removed), the precondition, postcondition and loop invariants as Lean
predicates, and the numbers of parameters and results. `Annotated.vc` is the **verification
condition**, computed by the verified generator `Silmaril.Wasm.Logic.VC.wpc`;
`Silmaril.Wasm.WatSpec.Thms.Annotated.sound` turns a proof of it into a valid every-run function
specification (`Annotated.spec`), at every profile and for every host relation.

```wat
(func $add (export "add") (param $x i32) (param $y i32) (result i32)
  (requires true)
  (ensures (result = x + y))
  local.get $x local.get $y i32.add)
```

The annotation language (the forms are removed before the WAT is parsed):

* `(requires P)`: `P` is a Lean proposition over the parameters, named as in WAT without `$`
  (`$x` is `x`; an unnamed parameter `k` is `p<k>`), of type `BitVec 32`/`BitVec 64` for
  `i32`/`i64`;
* `(ensures Q)`: over the parameters (their values on entry) and `result`, the single result;
* `(invariant I)`, placed inside a `loop`, before any nested `loop`: over the **current** values
  of the locals and parameters, by name; a parameter that the body writes (`local.set` or
  `local.tee`) is available on entry as `old_<name>`. The `k`-th invariant in the text belongs
  to the `k`-th loop in pre-order. The macro adds to it that the store is unchanged and the loop
  has no parameters.

Only `i32` and `i64` parameters, locals and at most one result are supported. The macro is
untrusted: whatever it produces, `Annotated.sound` holds; a wrong translation only gives an
unprovable condition.

`wat_spec!` and `wat_spec_st!` are **front-ends** of the canonical store-level form
`Silmaril.Wasm.Verify.FnSpec`: `Annotated.toFnSpec`/`AnnotatedSt.toFnSpec` state the same
specification as a `FnSpec` over argument lists of the right length (`Args n`), and
`Silmaril.Wasm.WatSpec.Thms` relates the conditions (`Annotated.vc_toFnSpec`,
`Annotated.verified`, `AnnotatedSt.toFnSpec_sound`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.WatSpec

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Logic.VC (wpc Invs)
open Silmaril.Wasm.Logic.Hoare (FSpec)

/-- **An annotated function**: a one-function module with its specification. -/
structure Annotated where
  /-- The plain module `(module (func …))`. -/
  module : Module
  /-- The precondition on the arguments. -/
  pre : List Val → Prop
  /-- The postcondition on the arguments and the results. -/
  post : List Val → List Val → Prop
  /-- The loop invariants, given the arguments and the initial store. -/
  inv : List Val → Store Nat → Invs Nat
  /-- The number of parameters. -/
  nparams : Nat
  /-- The number of results. -/
  nresults : Nat

/-- The function of the module. -/
@[simp] def Annotated.func (A : Annotated) : Func :=
  match A.module.funcs with
  | f :: _ => f
  | [] => ⟨⟨0⟩, [], []⟩

/-- **The verification condition**: for every module instance, store and arguments meeting the
precondition, there are `nparams` arguments, and the generator's condition holds for the body
in the callee's initial frame: every exit returns `nresults` values meeting the postcondition,
with the store unchanged. -/
@[simp] def Annotated.vc (A : Annotated) : Prop :=
  ∀ (mi : ModuleInst) (s : Store Nat) (args : List Val), A.pre args →
    args.length = A.nparams ∧
    wpc (A.inv args s) 0 A.func.body
      (Silmaril.Wasm.Logic.Exec.bodyPost A.nresults fun s' o =>
        s' = s ∧ ∃ res, o = .normal res ∧ A.post args res)
      s (Frame.forCall mi args A.func.locals) []

/-- **The specification** of the function instance `fi` at address `a`: on arguments meeting
the precondition, every run returns results meeting the postcondition and leaves the store
unchanged. -/
def Annotated.spec (A : Annotated) (fi : FuncInst Nat) (a : Nat) : FSpec Nat where
  pre s args := s.funcs[a]? = some fi ∧ A.pre args
  post s args s' o := s' = s ∧ ∃ res, o = .normal res ∧ A.post args res

/-- Argument lists of length `n`: the inputs of the `FnSpec` form of an annotated function. -/
abbrev Args (n : Nat) := {xs : List Val // xs.length = n}

/-- **The `FnSpec` form of an annotated function**: on argument lists of length `nparams`, the
same precondition, postcondition (the store unchanged) and loop invariants. -/
def Annotated.toFnSpec (A : Annotated) : Silmaril.Wasm.Verify.FnSpec (Args A.nparams) where
  args x := x.1
  nresults := A.nresults
  pre x _ _ := A.pre x.1
  post x _ s res s' := s' = s ∧ A.post x.1 res
  inv x _ s := A.inv x.1 s

/-! ## Functions over the store (`wat_spec_st!`)

`AnnotatedSt` is the form for functions that **read and write globals and memory**: the
precondition sees the module instance `mi` and the store `σ`, the postcondition the initial and
the final store `σ`, `σ'` (a relation: nothing is assumed unchanged), the loop invariants the
current store `σ` and the entry store `σ₀` (names in `wat_spec_st!`). Calls are verified modularly against a spec context
(`Silmaril.Wasm.Logic.VC.VCSpecs`, empty by default). Read-back of the store in annotations: `gv σ mi
k` (global `k` of the instance as 64 bits: `i64` as is, `i32` zero-extended, as
`Silmaril.Sim.X86Real.gv`), `mem σ mi a n` (the little-endian value of the `n` bytes at `a` of
memory `0`). -/

/-- An integer value as 64 bits (`i32` zero-extended, `0` for anything else). -/
def valNum : Val → BitVec 64
  | .num ⟨.int .i64, v⟩ => v
  | .num ⟨.int .i32, v⟩ => v.setWidth 64
  | _ => 0

/-- Global `k` of the instance `mi` as 64 bits (`0` if absent). -/
def gv {H : Type} (s : Store H) (mi : ModuleInst) (k : Nat) : BitVec 64 :=
  valNum ((Silmaril.Wasm.Logic.VC.globalVal s mi k).getD (Val.i64 0))

/-- The little-endian value of the `n` bytes at `a` of memory `0` of the instance (`0` if there is
no such memory; the bytes present). -/
def mem {H : Type} (s : Store H) (mi : ModuleInst) (a n : Nat) : Nat :=
  match mi.mems[0]? with
  | some ma => match s.mems[ma]? with
    | some m => Silmaril.Wasm.Logic.Core.leNat (Silmaril.Wasm.Logic.Core.bytesAt m.bytes ⟨a, n⟩)
    | none => 0
  | none => 0

/-- **An annotated function over the store.** -/
structure AnnotatedSt where
  /-- The plain module `(module … (func …))`. -/
  module : Module
  /-- The index of the annotated function among the module's functions. -/
  index : Nat
  /-- The precondition on the instance, the store and the arguments. -/
  pre : ModuleInst → Store Nat → List Val → Prop
  /-- The postcondition on the instance, the initial store, the arguments, the final store and
  the results. -/
  post : ModuleInst → Store Nat → List Val → Store Nat → List Val → Prop
  /-- The loop invariants, given the instance, the arguments and the entry store. -/
  inv : ModuleInst → List Val → Store Nat → Invs Nat
  /-- The number of parameters. -/
  nparams : Nat
  /-- The number of results. -/
  nresults : Nat

/-- The annotated function. -/
@[simp] def AnnotatedSt.func (A : AnnotatedSt) : Func :=
  (A.module.funcs[A.index]?).getD ⟨⟨0⟩, [], []⟩

/-- **The verification condition** (with the spec context `Γ` for calls): for every instance,
store and arguments meeting the precondition, the generator's condition for the body, every exit
returning `nresults` values (by falling through or `return`) related to the initial store and
arguments by the postcondition. No trap is allowed. -/
@[simp] def AnnotatedSt.vc (A : AnnotatedSt) (Γ : Silmaril.Wasm.Logic.VC.VCSpecs Nat := .empty) : Prop :=
  ∀ (mi : ModuleInst) (s : Store Nat) (args : List Val), A.pre mi s args →
    args.length = A.nparams ∧
    wpc (Γ := Γ) (A.inv mi args s) 0 A.func.body
      (Silmaril.Wasm.Logic.VC.fnPost A.nresults fun s' o =>
        ∃ res, o = .normal res ∧ A.post mi s args s' res)
      s (Frame.forCall mi args A.func.locals) []

/-- **The `FnSpec` form of a store-annotated function**: on argument lists of length `nparams`,
the same precondition, postcondition and loop invariants. Its condition (`FnSpec.vc`) is
stronger than `AnnotatedSt.vc`: no `return` (`bodyPost`, not `fnPost`) and no spec context. -/
def AnnotatedSt.toFnSpec (A : AnnotatedSt) : Silmaril.Wasm.Verify.FnSpec (Args A.nparams) where
  args x := x.1
  nresults := A.nresults
  pre x mi s := A.pre mi s x.1
  post x mi s res s' := A.post mi s x.1 s' res
  inv x mi s := A.inv mi x.1 s

/-- **The specification** of the function instance `fi` at address `a`. -/
def AnnotatedSt.spec (A : AnnotatedSt) (fi : FuncInst Nat) (a : Nat) : FSpec Nat where
  pre s args := s.funcs[a]? = some fi ∧ A.pre fi.module s args
  post s args s' o := ∃ res, o = .normal res ∧ A.post fi.module s args s' res

end Silmaril.Wasm.WatSpec

/-! ## The `wat_spec!` elaborator -/

public meta section

namespace Silmaril.Wasm.WatSpec.Elab

open Lean Elab Term Meta
open Silmaril.Wasm.Wat (Node parse)

/-- An annotation found in the text. -/
structure Annot where
  kind : String
  body : String

/-- Remove the annotation forms `(requires …)`, `(ensures …)`, `(invariant …)` from WAT text,
returning the remaining text and the annotations in textual order. Strings and comments of the
WAT text are skipped; parentheses inside an annotation must balance. -/
partial def strip (cs : List Char) (out : String) (acc : Array Annot) : Except String (String × Array Annot) :=
  match cs with
  | [] => .ok (out, acc)
  | '"' :: rest =>
    let rec str : List Char → String → Except String (List Char × String)
      | [], _ => .error "unterminated string in WAT"
      | '\\' :: c :: r, o => str r (o.push '\\' |>.push c)
      | '"' :: r, o => .ok (r, o.push '"')
      | c :: r, o => str r (o.push c)
    match str rest "\"" with
    | .ok (r, s) => strip r (out ++ s) acc
    | .error e => .error e
  | ';' :: ';' :: rest =>
    let line := rest.takeWhile (· ≠ '\n')
    strip (rest.drop line.length) (out ++ ";;" ++ String.ofList line) acc
  | '(' :: rest =>
    let word := String.ofList (rest.takeWhile fun c => c.isAlpha)
    if word == "requires" || word == "ensures" || word == "invariant" then
      let rec close : List Char → Nat → String → Except String (List Char × String)
        | [], _, _ => .error s!"unbalanced parentheses in ({word} …)"
        | ')' :: r, 0, o => .ok (r, o)
        | ')' :: r, n + 1, o => close r n (o.push ')')
        | '(' :: r, n, o => close r (n + 1) (o.push '(')
        | c :: r, n, o => close r n (o.push c)
      match close (rest.drop word.length) 0 "" with
      | .ok (r, body) => strip r (out.push ' ') (acc.push ⟨word, body.trimAscii.toString⟩)
      | .error e => .error e
    else strip rest (out.push '(') acc
  | c :: rest => strip rest (out.push c) acc

/-- A parameter or local: its Lean name and its WAT type (`i32` or `i64`). -/
structure Var where
  name : String
  ty : String
  deriving Inhabited

def bitsOf : String → Except String Nat
  | "i32" => .ok 32
  | "i64" => .ok 64
  | t => .error s!"wat_spec!: unsupported type {t} (only i32 and i64)"

def valCtor (ty : String) : String :=
  if ty == "i64" then "Silmaril.Wasm.Execution.Core.Val.i64" else "Silmaril.Wasm.Execution.Core.Val.i32"

/-- The declarations `(param …)`, `(local …)` or `(result …)` of a function node. -/
def decls (kind : String) (fields : List Node) (start : Nat) : List Var := Id.run do
  let mut out : Array Var := #[]
  for n in fields do
    match n with
    | .list _ (.atom _ k :: rest) =>
      if k == kind then
        match rest with
        | [.atom _ nm, .atom _ ty] =>
          if nm.startsWith "$" then
            out := out.push ⟨(nm.drop 1).toString, ty⟩
          else
            for t in [nm, ty] do
              out := out.push ⟨s!"p{start + out.size}", t⟩
        | ts =>
          for t in ts do
            match t with
            | .atom _ ty => out := out.push ⟨s!"p{start + out.size}", ty⟩
            | _ => pure ()
    | _ => pure ()
  return out.toList

/-- The local names and indices written by `local.set`/`local.tee` anywhere in the nodes. -/
partial def written (n : Node) : List String :=
  match n with
  | .list _ cs =>
    let rec go : List Node → List String
      | .atom _ op :: .atom _ x :: r =>
        (if op == "local.set" || op == "local.tee" then [x] else []) ++ go (.atom 0 x :: r)
      | c :: r => written c ++ go r
      | [] => []
    go cs
  | _ => []

def parseTerm (s : String) : TermElabM Term := do
  match Parser.runParserCategory (← getEnv) `term s "<wat_spec!>" with
  | .ok stx => pure ⟨stx⟩
  | .error e => throwError "wat_spec!: cannot parse `{s}`: {e}"

def binders (vs : List Var) : Except String String := do
  let mut out := ""
  for v in vs do
    out := out ++ s!" ({v.name} : BitVec {← bitsOf v.ty})"
  return out

def valList (vs : List Var) (names : List String) : String :=
  "[" ++ ", ".intercalate ((vs.zip names).map fun (v, n) => s!"{valCtor v.ty} {n}") ++ "]"

def ofExcept {α : Type} : Except String α → TermElabM α
  | .ok a => pure a
  | .error e => throwError e

/-- **`wat_spec!`**: an annotated WAT function (see the module docstring). -/
elab "wat_spec! " text:str : term => do
  let (plain, annots) ← ofExcept (strip text.getString.toList "" #[])
  let nodes ← ofExcept (parse plain)
  let func ← match nodes with
    | [f@(.list _ (.atom _ "func" :: _))] => pure f
    | _ => throwError "wat_spec!: expected exactly one (func …)"
  let fields := match func with | .list _ cs => cs | _ => []
  let params := decls "param" fields 0
  let results := decls "result" fields 0
  let locals := decls "local" fields params.length
  if results.length > 1 then throwError "wat_spec!: at most one result is supported"
  let req := (annots.find? (·.kind == "requires")).map (·.body) |>.getD "True"
  let ens := (annots.find? (·.kind == "ensures")).map (·.body) |>.getD "True"
  let invs := (annots.filter (·.kind == "invariant")).map (·.body)
  let wr := written func
  let isWritten (i : Nat) (v : Var) : Bool := wr.contains s!"${v.name}" || wr.contains s!"{i}"
  let pNames := params.map (·.name)
  let pBinders ← ofExcept (binders params)
  let argsEq := s!"args = {valList params pNames}"
  let preS := if params.isEmpty then s!"fun (args : List Silmaril.Wasm.Execution.Core.Val) => {argsEq} ∧ ({req})"
    else s!"fun (args : List Silmaril.Wasm.Execution.Core.Val) => ∃{pBinders}, {argsEq} ∧ ({req})"
  let resS ← match results with
    | [r] => pure s!"∃ (result : BitVec {← ofExcept (bitsOf r.ty)}), res = [{valCtor r.ty} result] ∧ ({ens})"
    | _ => pure s!"res = [] ∧ ({ens})"
  let postS := if params.isEmpty then
      s!"fun (args res : List Silmaril.Wasm.Execution.Core.Val) => {argsEq} → {resS}"
    else s!"fun (args res : List Silmaril.Wasm.Execution.Core.Val) => ∀{pBinders}, {argsEq} → {resS}"
  -- invariants: initial parameters (written ones as `old_x`), current values of written
  -- parameters and all locals
  let entry := params.zipIdx.map fun (v, i) => if isWritten i v then { v with name := s!"old_{v.name}" } else v
  let cur := (params.zipIdx.filter fun (v, i) => isWritten i v).map (·.1) ++ locals
  let entryB ← ofExcept (binders entry)
  let curB ← ofExcept (binders cur)
  let localNames := params.zipIdx.map (fun (v, i) => if isWritten i v then v.name else (entry[i]!).name) ++
    locals.map (·.name)
  let localsEq := "f.locals = [" ++ ", ".intercalate ((params ++ locals).zip localNames |>.map
    fun (v, n) => s!"some ({valCtor v.ty} {n})") ++ "]"
  let invBody (I : String) : String :=
    let inner := s!"s = s₀ ∧ a = [] ∧ " ++
      (if cur.isEmpty then s!"{localsEq} ∧ ({I})" else s!"∃{curB}, {localsEq} ∧ ({I})")
    if params.isEmpty then s!"args = [] ∧ {inner}"
    else s!"∃{entryB}, args = {valList params (entry.map (·.name))} ∧ {inner}"
  let arms := invs.toList.zipIdx.map fun (I, k) => s!"| {k} => {invBody I}"
  let invS := if invs.isEmpty then "fun _ _ _ _ _ _ => True" else s!"fun (args : List Silmaril.Wasm.Execution.Core.Val) (s₀ : Silmaril.Wasm.Execution.Core.Store Nat) (k : Nat) (s : Silmaril.Wasm.Execution.Core.Store Nat) (f : Silmaril.Wasm.Execution.Core.Frame) (a : List Silmaril.Wasm.Execution.Core.Val) => match k with " ++
    " ".intercalate arms ++ " | _ => True"
  let modT ← liftMacroM <| Silmaril.Wasm.Wat.Core.moduleTerm
    (fun scope nodes => Silmaril.Wasm.Wat.Core.instructions scope nodes) s!"(module {plain})"
  let preT ← parseTerm preS
  let postT ← parseTerm postS
  let invT ← parseTerm invS
  let np := Syntax.mkNumLit (toString params.length)
  let nr := Syntax.mkNumLit (toString results.length)
  let stx ← `(Silmaril.Wasm.WatSpec.Annotated.mk $modT $preT $postT $invT $np $nr)
  elabTerm stx (some (mkConst ``Silmaril.Wasm.WatSpec.Annotated))

end Silmaril.Wasm.WatSpec.Elab

public meta section

namespace Silmaril.Wasm.WatSpec.Elab

open Lean Elab Term Meta
open Silmaril.Wasm.Wat (Node parse)

/-- **`wat_spec_st! "$f" "(module …)"`**: the function `$f` of a WAT module, annotated with
`(requires P)`, `(ensures Q)` and `(invariant I)` over the store (see `AnnotatedSt`). In `P` the
names are the parameters, the instance `mi` and the store `σ`; in `Q` also the final store `σ'`
and `result`; in `I` the current values of the locals and parameters (`old_x` on entry for a
written parameter `x`), the entry store `σ₀` and the current store `σ`. Read-back functions:
`Silmaril.Wasm.WatSpec.gv`, `Silmaril.Wasm.WatSpec.mem`. All annotations of the text belong to `$f`.
Untrusted, as `wat_spec!`: `AnnotatedSt.sound` holds whatever it produces. -/
elab "wat_spec_st! " fname:str text:str : term => do
  let (plain, annots) ← ofExcept (strip text.getString.toList "" #[])
  let nodes ← ofExcept (parse plain)
  let fields ← match nodes with
    | [.list _ (.atom _ "module" :: args)] => pure args
    | _ => throwError "wat_spec_st!: expected one (module …)"
  let funcs := fields.filter fun n => match n with
    | .list _ (.atom _ "func" :: _) => true
    | _ => false
  let some idx := funcs.findIdx? (fun n => match n with
      | .list _ (.atom _ "func" :: .atom _ nm :: _) => nm == fname.getString
      | _ => false)
    | throwError "wat_spec_st!: no function {fname.getString}"
  let func := funcs[idx]!
  let ffields := match func with | .list _ cs => cs | _ => []
  let params := decls "param" ffields 0
  let results := decls "result" ffields 0
  let locals := decls "local" ffields params.length
  if results.length > 1 then throwError "wat_spec_st!: at most one result is supported"
  let req := (annots.find? (·.kind == "requires")).map (·.body) |>.getD "True"
  let ens := (annots.find? (·.kind == "ensures")).map (·.body) |>.getD "True"
  let invs := (annots.filter (·.kind == "invariant")).map (·.body)
  let wr := written func
  let isWritten (i : Nat) (v : Var) : Bool := wr.contains s!"${v.name}" || wr.contains s!"{i}"
  let pNames := params.map (·.name)
  let pBinders ← ofExcept (binders params)
  let V := "Silmaril.Wasm.Execution.Core.Val"
  let S := "Silmaril.Wasm.Execution.Core.Store Nat"
  let MI := "Silmaril.Wasm.Execution.Core.ModuleInst"
  let argsEq := s!"args = {valList params pNames}"
  let preS := if params.isEmpty then
      s!"fun (mi : {MI}) (σ : {S}) (args : List {V}) => {argsEq} ∧ ({req})"
    else s!"fun (mi : {MI}) (σ : {S}) (args : List {V}) => ∃{pBinders}, {argsEq} ∧ ({req})"
  let resS ← match results with
    | [r] => pure s!"∃ (result : BitVec {← ofExcept (bitsOf r.ty)}), res = [{valCtor r.ty} result] ∧ ({ens})"
    | _ => pure s!"res = [] ∧ ({ens})"
  let postS := if params.isEmpty then
      s!"fun (mi : {MI}) (σ : {S}) (args : List {V}) (σ' : {S}) (res : List {V}) => {argsEq} → {resS}"
    else s!"fun (mi : {MI}) (σ : {S}) (args : List {V}) (σ' : {S}) (res : List {V}) => ∀{pBinders}, {argsEq} → {resS}"
  let entry := params.zipIdx.map fun (v, i) => if isWritten i v then { v with name := s!"old_{v.name}" } else v
  let cur := (params.zipIdx.filter fun (v, i) => isWritten i v).map (·.1) ++ locals
  let entryB ← ofExcept (binders entry)
  let curB ← ofExcept (binders cur)
  let localNames := params.zipIdx.map (fun (v, i) => if isWritten i v then v.name else (entry[i]!).name) ++
    locals.map (·.name)
  let localsEq := "f.locals = [" ++ ", ".intercalate ((params ++ locals).zip localNames |>.map
    fun (v, n) => s!"some ({valCtor v.ty} {n})") ++ "]"
  let invBody (I : String) : String :=
    let inner := s!"a = [] ∧ " ++
      (if cur.isEmpty then s!"{localsEq} ∧ ({I})" else s!"∃{curB}, {localsEq} ∧ ({I})")
    if params.isEmpty then s!"args = [] ∧ {inner}"
    else s!"∃{entryB}, args = {valList params (entry.map (·.name))} ∧ {inner}"
  let arms := invs.toList.zipIdx.map fun (I, k) => s!"| {k} => {invBody I}"
  let invS := if invs.isEmpty then "fun _ _ _ _ _ _ _ => True" else
    s!"fun (mi : {MI}) (args : List {V}) (σ₀ : {S}) (k : Nat) (σ : {S}) (f : Silmaril.Wasm.Execution.Core.Frame) (a : List {V}) => match k with " ++
    " ".intercalate arms ++ " | _ => True"
  let modT ← liftMacroM <| Silmaril.Wasm.Wat.Core.moduleTerm
    (fun scope nodes => Silmaril.Wasm.Wat.Core.instructions scope nodes) plain
  let preT ← parseTerm preS
  let postT ← parseTerm postS
  let invT ← parseTerm invS
  let ix := Syntax.mkNumLit (toString idx)
  let np := Syntax.mkNumLit (toString params.length)
  let nr := Syntax.mkNumLit (toString results.length)
  let stx ← `(Silmaril.Wasm.WatSpec.AnnotatedSt.mk $modT $ix $preT $postT $invT $np $nr)
  elabTerm stx (some (mkConst ``Silmaril.Wasm.WatSpec.AnnotatedSt))

end Silmaril.Wasm.WatSpec.Elab
