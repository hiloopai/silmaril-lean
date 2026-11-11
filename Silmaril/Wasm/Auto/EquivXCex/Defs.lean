module

public import Silmaril.Wasm.Auto.Equiv.Thms
public import Silmaril.Wasm.Game.Signature.Defs

/-!
# Counterexamples for the extended checker: definitions

The extended checker of `Silmaril.Wasm.Auto.Equiv` answers `false` when the normal forms differ,
which is not a refutation. This module adds **differential testing** on the symbolic runs: the
final states (or the trap at the first failing guard) of both segments are evaluated in probe
environments and probe memories, in a canonical concrete context, and compared.

* `ctxOf lt st gt ρ B0`: the canonical typed context: a store with the globals `0 … k-1` holding
  the input values of `ρ` and one memory with bytes `B0`; a frame with the input locals whose
  module maps global `k` to address `k` and memory `0` to address `0`;
* `viewOut loc s F o`: what the comparison looks at: global values, memory bytes, the locals
  when `loc`, and the results of a normal outcome;
* `outView loc c mem S`: that view of the outcome of a symbolic run `S` in the context `c`;
* `cexAtX loc lt st gt mem a b xs B0`: the inputs `xs` (`Equiv.envOf`) and initial memory `B0`
  make the two views differ (`loc = true` for `SegEquivX`, `false` for `OutEquivX`);
* `probeMems`, `findCexX`: the search over `Equiv.probeEnvs` and three probe memories (empty, 32
  zero bytes, 32 patterned bytes).

The refutation theorems are `not_segEquivX_of_cex` and `not_outEquivX_of_cex`
(`Silmaril.Wasm.Auto.EquivXCex.Thms`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.EquivXCex

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Auto.Equiv (Env envOf probeEnvs)
open Silmaril.Wasm.Auto.Equiv

/-- The type of a mutable integer global. -/
def gty (t : IntType) : CGlobalType := ⟨.var, (Silmaril.Wasm.Game.ScalarType.num (.int t)).toC⟩

/-- A memory instance with the bytes `B0`. -/
def memOf (B0 : ByteArray) : MemInst := { noMem with bytes := B0 }

/-- **The canonical typed context** of the inputs `ρ` and the initial memory `B0`. -/
def ctxOf (lt st gt : List IntType) (ρ : Env) (B0 : ByteArray) : XCtx Nat where
  s := { globals := (initX lt st gt).globs.map fun p => ⟨gty p.1, denX ρ B0 p⟩, mems := [memOf B0] }
  f := { locals := (initX lt st gt).locals.map fun p => some (denX ρ B0 p),
         module := { globals := List.range gt.length, mems := [0] } }
  ρ := ρ
  ga := List.range gt.length
  ma := 0
  mi := memOf B0

/-- The observable part of an outcome: global values, memory bytes, locals (when `loc`) and the
results of a normal outcome. -/
def viewOut (loc : Bool) (s : Store Nat) (F : Frame) (o : Outcome) :
    List Val × List ByteArray × List (Option Val) × Option (List Val) :=
  (s.globals.map (·.value), s.mems.map (·.bytes), if loc then F.locals else [],
    match o with
    | .normal vs => some vs
    | _ => none)

/-- The view of the outcome of a symbolic run in a context. -/
def outView (loc : Bool) (c : XCtx Nat) (mem : Bool) (S : XState) :
    List Val × List ByteArray × List (Option Val) × Option (List Val) :=
  match firstFail c.ρ c.mi.bytes S.guards with
  | some T => viewOut loc (c.storeOf mem T) (c.frameOf T) .trap
  | none => viewOut loc (c.storeOf mem S) (c.frameOf S) (.normal (c.stackOf S).reverse)

/-- **A counterexample**: the views of the two runs differ in the canonical context. -/
def cexAtX (loc : Bool) (lt st gt : List IntType) (mem : Bool) (a b : List Instr) (xs : List Nat)
    (B0 : ByteArray) : Bool :=
  match xsexec mem (initX lt st gt) a, xsexec mem (initX lt st gt) b with
  | some A, some B =>
    let c := ctxOf lt st gt (envOf xs) B0
    decide (outView loc c mem A ≠ outView loc c mem B)
  | _, _ => false

/-- Probe memories: empty, 32 zero bytes, 32 patterned bytes. -/
def probeMems : List ByteArray :=
  [ByteArray.empty, ⟨Array.replicate 32 0⟩, ⟨(Array.range 32).map fun i => UInt8.ofNat (i * 37 + 11)⟩]

/-- **Differential testing** of the extended checker's runs: the first probe environment and
memory (by index in `probeMems`) that is a counterexample. -/
def findCexX (loc : Bool) (lt st gt : List IntType) (mem : Bool) (a b : List Instr) :
    Option (List Nat × Nat) :=
  let envs := probeEnvs (lt.length + st.length + gt.length)
  let cands := (List.range (if mem then probeMems.length else 1)).flatMap fun k => envs.map fun xs => (xs, k)
  cands.find? fun p => cexAtX loc lt st gt mem a b p.1 (probeMems.getD p.2 ByteArray.empty)

end Silmaril.Wasm.Auto.EquivXCex
