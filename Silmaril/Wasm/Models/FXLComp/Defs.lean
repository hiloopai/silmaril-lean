module

public import Silmaril.Wasm.Models.FXL.Defs
public import Silmaril.Wasm.Models.FXT.Defs
public import Silmaril.Wasm.V2.ToCore.Types

/-!
# Compiling `StepFXL` programs to FX code over the `StepFXT` intrinsics

`StepFXL` (`Silmaril.Wasm.Models.FXL`) is a separate machine with continuation-valued locals, the
queue and the log built in. This module compiles its programs to FX functions of `StepFX'`
(`Silmaril.Wasm.Models.FXV`) that call the intrinsics of `StepFXT` (`Silmaril.Wasm.Models.FXT`) for
everything `StepFX'` lacks:

* every **local** `i` of function `g` is the continuation cell `base g + i` (`cget`, `cset`),
  where `base` lays out the parameters and locals of the functions one after the other; a
  `call g` stores its arguments in the cells of `g` (`cset`, last argument first) and then calls
  `g` without parameters; the body of `g` starts by setting its other locals to `ref.null`
  (read from the cell `nullCell`, which nothing writes). So a function's locals are shared by
  its activations: the compilation is faithful for programs in which **no function with
  locals is active twice at the same time** (true of the explainer's schedulers, which run one
  after the other);
* `ref.null` reads `nullCell`; `ref.is_null`, `print_i32` and the queue are the intrinsics
  `isNull`, `log`, `enq`, `deq`, `qEmpty`;
* `ref.func f; cont.new`, `resume` with `(on $t $l)` clauses and `suspend` are the FX
  instructions; `block n`, `loop`, `if`, `br`, `return` the structured ones (block type
  `typeIdx n` is `[] → [i32^n]`; types are unused by the untyped `StepFX'` beyond arities).

**The setting** of a program `P` with `nt` tags: host codes `0 … |P|-1` are the compiled FX
functions (`fxOf`), the next ones the intrinsics (`intrOf`: `log`, `enq`, `deq`, `qEmpty`,
`isNull`, then `cget i`, `cset i` for each cell); function and tag addresses are indices, all
in one module instance `modOf`. `initT P f` calls function `f` with empty cells, queue and
log; `logV` reads a `StepFXL` log as `i32` values.

Not here: a general simulation theorem from `StepFXL` runs to `StepFXT` runs of the compiled
program (open, docs/projects/wasm-wasi.md); the explainer's programs are checked one by one
(`Silmaril.Wasm.FX.Examples.ThreadsT`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXLComp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXT
open Silmaril.Wasm.Models.FXL (I Fn Prog)

/-- An index. -/
def ix {k : IndexKind} (j : Nat) : Idx k := ⟨⟨j % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩

/-! ## Layout -/

/-- The first cell of function `g`. -/
def base (P : Prog) (g : Nat) : Nat := ((P.take g).map fun F => F.np + F.nl).sum

/-- The number of cells of the locals. -/
def nLocals (P : Prog) : Nat := (P.map fun F => F.np + F.nl).sum

/-- The cell holding `ref.null` (never written). -/
def nullCell (P : Prog) : Nat := nLocals P

/-- The host codes of the intrinsics. -/
def cLog (P : Prog) : Nat := P.length
def cEnq (P : Prog) : Nat := P.length + 1
def cDeq (P : Prog) : Nat := P.length + 2
def cQEmpty (P : Prog) : Nat := P.length + 3
def cIsNull (P : Prog) : Nat := P.length + 4
def cGet (P : Prog) (i : Nat) : Nat := P.length + 5 + 2 * i
def cSet (P : Prog) (i : Nat) : Nat := P.length + 6 + 2 * i

/-- The number of host codes (functions and intrinsics). -/
def nCodes (P : Prog) : Nat := P.length + 5 + 2 * (nullCell P + 1)

/-- The intrinsic of a host code. -/
def intrOf (P : Prog) (h : Nat) : Option Intr :=
  if h < P.length then none
  else
    match h - P.length with
    | 0 => some .log
    | 1 => some .enq
    | 2 => some .deq
    | 3 => some .qEmpty
    | 4 => some .isNull
    | j + 5 => if j % 2 = 0 then some (.cget (j / 2)) else some (.cset (j / 2))

/-! ## Code -/

/-- Call host code `j`: `ref.func j; call_ref`. -/
def callC (j : Nat) : List InstrFX := [.core (.refFunc (ix j)), .core (.callRef (ix 0))]

/-- Store the `np` arguments on the stack in the cells from `b` (last argument first). -/
def storeArgs (P : Prog) (b np : Nat) : List InstrFX :=
  ((List.range np).reverse.map fun j => callC (cSet P (b + j))).flatten

/-- Set `nl` locals from cell `b` to `ref.null`. -/
def nullLocals (P : Prog) (b nl : Nat) : List InstrFX :=
  ((List.range nl).map fun j => callC (cGet P (nullCell P)) ++ callC (cSet P (b + j))).flatten

mutual
/-- **Compile an instruction** of function `g`. -/
def compI (P : Prog) (g : Nat) : I → List InstrFX
  | .const n => [.core (.intConst .i32 (BitVec.ofInt 32 n))]
  | .refNull => callC (cGet P (nullCell P))
  | .refIsNull => callC (cIsNull P)
  | .drop => [.core .drop]
  | .localGet x => callC (cGet P (base P g + x))
  | .localSet x => callC (cSet P (base P g + x))
  | .call f =>
    match P[f]? with
    | some F => storeArgs P (base P f) F.np ++ callC f
    | none => [.core .unreachable]
  | .log => callC (cLog P)
  | .qEmpty => callC (cQEmpty P)
  | .enq => callC (cEnq P)
  | .deq => callC (cDeq P)
  | .contNew f => [.core (.refFunc (ix f)), .fx (.contNew (ix 0))]
  | .resume hs => [.fx (.resume (ix 0) (hs.map fun p => .onLabel (ix p.1) (ix p.2)))]
  | .suspend t => [.fx (.suspend (ix t))]
  | .block n body => [.block (.typeIdx (ix n)) (compL P g body)]
  | .loop body => [.loop (.typeIdx (ix 0)) (compL P g body)]
  | .if_ thn els => [.if_ (.typeIdx (ix 0)) (compL P g thn) (compL P g els)]
  | .br l => [.core (.br (ix l))]
  | .ret => [.core .return_]

/-- Compile code of function `g`. -/
def compL (P : Prog) (g : Nat) : List I → List InstrFX
  | [] => []
  | i :: is => compI P g i ++ compL P g is
end

/-! ## The setting -/

/-- `i32`. -/
abbrev ti32 : CValType := .num (.int .i32)

/-- The module types: type `n` is `[] → [i32^n]`, `n < 4`. -/
def typesC : List DefType :=
  (List.range 4).map fun n =>
    Silmaril.Wasm.V2.FuncType.toDefType ⟨[], List.replicate n (.num (.int .i32))⟩

/-- The module instance: every host code is a function, `nt` tags. -/
def modOf (P : Prog) (nt : Nat) : ModuleInst :=
  { types := typesC, tags := List.range nt, funcs := List.range (nCodes P) }

/-- **The compiled FX functions.** -/
def fxOf (P : Prog) (nt : Nat) (h : Nat) : Option FuncFX :=
  match P[h]? with
  | some F =>
    some ⟨modOf P nt, 0, F.nr, [],
      nullLocals P (base P h + F.np) F.nl ++ compL P h F.body⟩
  | none => none

/-- The store: one host function per code, `nt` tags. -/
def storeOf (P : Prog) (nt : Nat) : Store Nat :=
  { funcs := (List.range (nCodes P)).map fun h => ⟨typesC.head!, modOf P nt, .host h⟩,
    tags := (List.range nt).map fun _ => ⟨typesC.head!⟩ }

/-- The empty table: every cell `ref.null`. -/
def tblOf (P : Prog) : Tbl :=
  ⟨List.replicate (nullCell P + 1) (.val (.ref .null)), [], []⟩

/-- **The initial configuration**: call function `f`. -/
def initT (P : Prog) (nt : Nat) (f : Nat) : ConfigT Nat :=
  ⟨⟨storeOf P nt, [], ⟨[], modOf P nt⟩, (callC f).map InstrFX.toAdmin⟩, tblOf P⟩

/-- A `StepFXL` log as `i32` values. -/
def logV (l : List Int) : List Val := l.map fun n => Val.i32 (BitVec.ofInt 32 n)

end Silmaril.Wasm.Models.FXLComp
