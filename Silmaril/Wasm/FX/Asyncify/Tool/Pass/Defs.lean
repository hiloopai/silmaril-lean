module

public import Silmaril.Wasm.FX.Asyncify.Tool.Frag.Defs

/-!
# The asyncify pass, first strategy: unwinding to a shadow stack, guarded re-entry

The pass turns a source program (`Prog`, suspending imports) into plain Core code that never calls
an import. The strategy is Binaryen's Asyncify, in its whole-program form, with the host protocol
of returning to the host instead of calling it:

* two mutable `i32` globals: `state` (global 0: 0 normal, 1 unwinding, 2 rewinding) and `sp`
  (global 1: the shadow-stack pointer, a byte address); one memory holding the request area
  (bytes `[0, 4 R)`, `R = P.reqWords`) and the shadow stack (from `SB = 4 R`);
* every function gets `F = P.frameWords` locals in all: its own, padding, and the resume index
  `sel` (local `F - 1`); a saved frame is `F` words: locals `0 … F-2`, then the index of the call
  statement it waits on;
* **prologue**: when rewinding, pop a frame record (`sp -= 4F`) and reload every local;
* a **pure statement** runs only when not rewinding (`if state ≠ 2`);
* a **call statement `k` to a defined function** runs when not rewinding or when `sel = k`
  (re-entering the callee, which rewinds itself); after the call, if the callee started an unwind
  (`state = 1`), save the frame with index `k` and return dummy results;
* a **call statement `k` to an import** (a suspension point): in normal mode write the request
  (the import index, then the arguments) at address 0, set `state := 1`, save the frame and return
  dummies; when rewinding with `sel = k`, set `state := 0` and push the host's answers (words
  `0 … m-1`) for the statement's `local.set`s;
* the tail is unchanged.

`asyncifyProg` is the machine program of the output, `asyncifyModule` the Core module (the same
types and imports; the two globals, one memory and the exports `asyncify_state` and
`asyncify_memory` are added). The host protocol is `Silmaril.Wasm.FX.Asyncify.Tool.Sys`.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

/-- A local index from a number. -/
def lidx (i : Nat) : LocalIdx := ⟨Fin.ofNat _ i⟩

/-- An `i32.const`. -/
def c32 (n : Nat) : Instr := .intConst .i32 (BitVec.ofNat 32 n)

/-- The memory argument of a word access at offset `o`. -/
def marg (o : Nat) : MemArg := ⟨2, Fin.ofNat _ o⟩

/-- Load a word at offset `o`. -/
def ld (o : Nat) : Instr := .intLoad .i32 none ⟨0⟩ (marg o)

/-- Store a word at offset `o`. -/
def st (o : Nat) : Instr := .intStore .i32 none ⟨0⟩ (marg o)

/-- `global.get state`, `global.set state`, `global.get sp`, `global.set sp`. -/
def gState : Instr := .globalGet ⟨0⟩
def sState : Instr := .globalSet ⟨0⟩
def gSp : Instr := .globalGet ⟨1⟩
def sSp : Instr := .globalSet ⟨1⟩

/-- `i32.eq`, `i32.ne`, `i32.or`, `i32.add`, `i32.sub`. -/
def eqI : Instr := .intRelOp .i32 .eq
def neI : Instr := .intRelOp .i32 .ne
def orI : Instr := .intBinOp .i32 .or
def addI : Instr := .intBinOp .i32 .add
def subI : Instr := .intBinOp .i32 .sub

/-- An `if` without results and without an else arm. -/
def ifThen (t : List Instr) : Instr := .if_ .empty t []

/-- Store locals `i, …, i+n-1` at offsets `4i, …` from `sp`. -/
def saveLocals : Nat → Nat → List Instr
  | _, 0 => []
  | i, n + 1 => [gSp, .localGet (lidx i), st (4 * i)] ++ saveLocals (i + 1) n

/-- Reload locals `i, …, i+n-1` from offsets `4i, …` from `sp`. -/
def loadLocals : Nat → Nat → List Instr
  | _, 0 => []
  | i, n + 1 => [gSp, ld (4 * i), .localSet (lidx i)] ++ loadLocals (i + 1) n

/-- Save the frame (frame size `F` words) waiting on statement `k`, and push it. -/
def saveCode (F k : Nat) : List Instr :=
  saveLocals 0 (F - 1) ++ [gSp, c32 k, st (4 * (F - 1)), gSp, c32 (4 * F), addI, sSp]

/-- Pop a frame record and reload every local. -/
def restoreCode (F : Nat) : List Instr := [gSp, c32 (4 * F), subI, sSp] ++ loadLocals 0 F

/-- The prologue: when rewinding, restore the frame. -/
def prologue (F : Nat) : List Instr := [gState, c32 2, eqI, ifThen (restoreCode F)]

/-- `n` dummy results. -/
def dummies (n : Nat) : List Instr := List.replicate n (c32 0)

/-- After a call to a defined function: if it started an unwind, save and return. -/
def chk (F k n : Nat) : List Instr :=
  [gState, c32 1, eqI, ifThen (saveCode F k ++ dummies n ++ [.return_])]

/-- Push the host's `m` answers (words `0 … m-1`). -/
def pushAns : Nat → Nat → List Instr
  | _, 0 => []
  | j, m + 1 => [c32 0, ld (4 * j)] ++ pushAns (j + 1) m

/-- Write the arguments (from locals) at words `j, j+1, …`. -/
def reqArgs : Nat → List LocalIdx → List Instr
  | _, [] => []
  | j, a :: as => [c32 0, .localGet a, st (4 * j)] ++ reqArgs (j + 1) as

/-- Write the request of import `f`: its index, then the arguments. -/
def reqCode (f : FuncIdx) (as : List LocalIdx) : List Instr :=
  [c32 0, c32 f.value.val, st 0] ++ reqArgs 1 as

/-- The parameters of the translation: number of imports, frame size, result count of the
function. -/
structure TrCtx where
  nimp : Nat
  F : Nat
  nres : Nat

/-- The translation of statement `k`. -/
def trStmt (X : TrCtx) (k : Nat) : Stmt → List Instr
  | .pure is => [gState, c32 2, neI, ifThen is]
  | .call f as rs =>
    if f.value.val < X.nimp then
      [gState, c32 2, eqI,
        .if_ .empty
          [.localGet (lidx (X.F - 1)), c32 k, eqI,
            ifThen ([c32 0, sState] ++ pushAns 0 rs.length ++ setsCode rs)]
          (reqCode f as ++ [c32 1, sState] ++ saveCode X.F k ++ dummies X.nres ++ [.return_])]
    else
      [gState, c32 2, neI, .localGet (lidx (X.F - 1)), c32 k, eqI, orI,
        ifThen (getsCode as ++ [.call f] ++ chk X.F k X.nres ++ setsCode rs)]

/-- The translation of statements `k, k+1, …`. -/
def trS (X : TrCtx) : Nat → List Stmt → List Instr
  | _, [] => []
  | k, s :: r => trStmt X k s ++ trS X (k + 1) r

/-- The translation context of a function. -/
def Prog.ctx (P : Prog) (fn : FnSrc) : TrCtx := ⟨P.imps.length, P.frameWords, fn.nres⟩

/-- The asyncified body. -/
def Prog.tBody (P : Prog) (fn : FnSrc) : List Instr :=
  prologue P.frameWords ++ trS (P.ctx fn) 0 fn.stmts ++ fn.tail

/-- The machine program of the output: every function has `F` locals in all. -/
def asyncifyProg (P : Prog) : Env :=
  ⟨P.imps, P.fns.map fun fn => ⟨fn.nparams, P.frameWords - fn.nparams, fn.nres, P.tBody fn⟩⟩

/-- The start of the shadow stack (bytes). -/
def Prog.sb (P : Prog) : Nat := 4 * P.reqWords

/-- The initial globals of the output: `state = 0`, `sp = SB`. -/
def Prog.tGlobals (P : Prog) : List W := [0, BitVec.ofNat 32 P.sb]

/-! ## The output module -/

/-- The names of the added exports. -/
def stateExport : String := "asyncify_state"
def memoryExport : String := "asyncify_memory"

/-- A mutable `i32` global with a constant initialiser. -/
def mutI32 (n : Nat) : Global := ⟨⟨.var, .i32⟩, [c32 n]⟩

/-- The output module: the input's types, imports and exports, the asyncified functions, the
globals `state` and `sp`, and one memory of `pages` pages. -/
def asyncifyModule (m : Module) (P : Prog) (pages : Nat) : Module :=
  { m with
    globals := [mutI32 0, mutI32 P.sb]
    memories := [⟨.i32, ⟨Fin.ofNat _ pages, none⟩⟩]
    funcs := (m.funcs.zip P.fns).map fun (f, fn) =>
      ⟨f.type, List.replicate (P.frameWords - fn.nparams) .i32, P.tBody fn⟩
    exports := m.exports ++ [⟨stateExport, .global ⟨0⟩⟩, ⟨memoryExport, .memory ⟨0⟩⟩] }

/-- The pass on modules: recognise, then transform. `pages` is the memory size; the request area
and the shadow stack must fit, which the host protocol does not check (an overflow traps in Core,
see `docs/projects/wasm-binaryen-tooling.md`). -/
def asyncify (m : Module) (pages : Nat := 1) : Except String Module :=
  match recognize m with
  | .error e => .error e
  | .ok P =>
    if m.exports.any (fun e => e.name == stateExport || e.name == memoryExport) then
      .error "the module already exports asyncify_state or asyncify_memory"
    else if P.sb + 4 * P.frameWords ≤ 65536 * pages ∧ pages < 65536 then
      .ok (asyncifyModule m P pages)
    else .error "the memory cannot hold the request area and one frame"

end Silmaril.Wasm.FX.Asyncify.Tool
