module

public import Silmaril.Wasm.WatSpec.Defs

/-!
# Annotated WAT over the store: the G accessors of the x86 simulator

`rgetA`, `rsetA`, `fset6A` are three of the five state accessors of the G representation of the
x86-64 simulator (`examples/wasm-sim/solvers/gm-split/acc-g.wat`, stream solvers, generated
from rt-x86's `src/state-g.wat`), quoted with `wat_spec_st!` (each with the 24 location globals)
and annotated over the store: `rget` returns global `r`, `rset` and `fset6` **write globals**;
their postconditions state the final store (`setGlobalIdx`), from which the read-back relations
(`gv`, as `Silmaril.Sim.X86Real.repG`) follow. Proofs: `Silmaril.Proofs.Wasm.Examples.WatSpecSt.Acc`.
A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.WatSpecSt

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.WatSpec Silmaril.Wasm.Logic.VC

def rgetA : AnnotatedSt := wat_spec_st! "$rget" r#"(module
  (global $r0 (mut i64) (i64.const 0))
  (global $r1 (mut i64) (i64.const 0))
  (global $r2 (mut i64) (i64.const 0))
  (global $r3 (mut i64) (i64.const 0))
  (global $r4 (mut i64) (i64.const 0))
  (global $r5 (mut i64) (i64.const 0))
  (global $r6 (mut i64) (i64.const 0))
  (global $r7 (mut i64) (i64.const 0))
  (global $r8 (mut i64) (i64.const 0))
  (global $r9 (mut i64) (i64.const 0))
  (global $r10 (mut i64) (i64.const 0))
  (global $r11 (mut i64) (i64.const 0))
  (global $r12 (mut i64) (i64.const 0))
  (global $r13 (mut i64) (i64.const 0))
  (global $r14 (mut i64) (i64.const 0))
  (global $r15 (mut i64) (i64.const 0))
  (global $rip (mut i64) (i64.const 0))
  (global $cf (mut i32) (i32.const 0))
  (global $pf (mut i32) (i32.const 0))
  (global $af (mut i32) (i32.const 0))
  (global $zf (mut i32) (i32.const 0))
  (global $sf (mut i32) (i32.const 0))
  (global $of (mut i32) (i32.const 0))
  (global $df (mut i32) (i32.const 0))
  (func $rget (param $r i32) (result i64)
    (requires (∃ w : BitVec 64, r.toNat < 17 ∧ globalVal σ mi r.toNat = some (Val.i64 w)))
    (ensures (σ' = σ ∧ result = gv σ mi r.toNat))
    (block $default
    (block $L16
    (block $L15
    (block $L14
    (block $L13
    (block $L12
    (block $L11
    (block $L10
    (block $L9
    (block $L8
    (block $L7
    (block $L6
    (block $L5
    (block $L4
    (block $L3
    (block $L2
    (block $L1
    (block $L0
      (br_table $L0 $L1 $L2 $L3 $L4 $L5 $L6 $L7 $L8 $L9 $L10 $L11 $L12 $L13 $L14 $L15 $L16 $default (local.get $r)))
      (return (global.get $r0)))
      (return (global.get $r1)))
      (return (global.get $r2)))
      (return (global.get $r3)))
      (return (global.get $r4)))
      (return (global.get $r5)))
      (return (global.get $r6)))
      (return (global.get $r7)))
      (return (global.get $r8)))
      (return (global.get $r9)))
      (return (global.get $r10)))
      (return (global.get $r11)))
      (return (global.get $r12)))
      (return (global.get $r13)))
      (return (global.get $r14)))
      (return (global.get $r15)))
      (return (global.get $rip)))
    (unreachable))
)"#

def rsetA : AnnotatedSt := wat_spec_st! "$rset" r#"(module
  (global $r0 (mut i64) (i64.const 0))
  (global $r1 (mut i64) (i64.const 0))
  (global $r2 (mut i64) (i64.const 0))
  (global $r3 (mut i64) (i64.const 0))
  (global $r4 (mut i64) (i64.const 0))
  (global $r5 (mut i64) (i64.const 0))
  (global $r6 (mut i64) (i64.const 0))
  (global $r7 (mut i64) (i64.const 0))
  (global $r8 (mut i64) (i64.const 0))
  (global $r9 (mut i64) (i64.const 0))
  (global $r10 (mut i64) (i64.const 0))
  (global $r11 (mut i64) (i64.const 0))
  (global $r12 (mut i64) (i64.const 0))
  (global $r13 (mut i64) (i64.const 0))
  (global $r14 (mut i64) (i64.const 0))
  (global $r15 (mut i64) (i64.const 0))
  (global $rip (mut i64) (i64.const 0))
  (global $cf (mut i32) (i32.const 0))
  (global $pf (mut i32) (i32.const 0))
  (global $af (mut i32) (i32.const 0))
  (global $zf (mut i32) (i32.const 0))
  (global $sf (mut i32) (i32.const 0))
  (global $of (mut i32) (i32.const 0))
  (global $df (mut i32) (i32.const 0))
  (func $rset (param $r i32) (param $v i64)
    (requires (r.toNat < 17 ∧ (globalVal σ mi r.toNat).isSome))
    (ensures (σ' = setGlobalIdx σ mi r.toNat (Val.i64 v)))
    (block $default
    (block $L16
    (block $L15
    (block $L14
    (block $L13
    (block $L12
    (block $L11
    (block $L10
    (block $L9
    (block $L8
    (block $L7
    (block $L6
    (block $L5
    (block $L4
    (block $L3
    (block $L2
    (block $L1
    (block $L0
      (br_table $L0 $L1 $L2 $L3 $L4 $L5 $L6 $L7 $L8 $L9 $L10 $L11 $L12 $L13 $L14 $L15 $L16 $default (local.get $r)))
      (global.set $r0 (local.get $v)) (return))
      (global.set $r1 (local.get $v)) (return))
      (global.set $r2 (local.get $v)) (return))
      (global.set $r3 (local.get $v)) (return))
      (global.set $r4 (local.get $v)) (return))
      (global.set $r5 (local.get $v)) (return))
      (global.set $r6 (local.get $v)) (return))
      (global.set $r7 (local.get $v)) (return))
      (global.set $r8 (local.get $v)) (return))
      (global.set $r9 (local.get $v)) (return))
      (global.set $r10 (local.get $v)) (return))
      (global.set $r11 (local.get $v)) (return))
      (global.set $r12 (local.get $v)) (return))
      (global.set $r13 (local.get $v)) (return))
      (global.set $r14 (local.get $v)) (return))
      (global.set $r15 (local.get $v)) (return))
      (global.set $rip (local.get $v)) (return))
    (unreachable))
)"#

def fset6A : AnnotatedSt := wat_spec_st! "$fset6" r#"(module
  (global $r0 (mut i64) (i64.const 0))
  (global $r1 (mut i64) (i64.const 0))
  (global $r2 (mut i64) (i64.const 0))
  (global $r3 (mut i64) (i64.const 0))
  (global $r4 (mut i64) (i64.const 0))
  (global $r5 (mut i64) (i64.const 0))
  (global $r6 (mut i64) (i64.const 0))
  (global $r7 (mut i64) (i64.const 0))
  (global $r8 (mut i64) (i64.const 0))
  (global $r9 (mut i64) (i64.const 0))
  (global $r10 (mut i64) (i64.const 0))
  (global $r11 (mut i64) (i64.const 0))
  (global $r12 (mut i64) (i64.const 0))
  (global $r13 (mut i64) (i64.const 0))
  (global $r14 (mut i64) (i64.const 0))
  (global $r15 (mut i64) (i64.const 0))
  (global $rip (mut i64) (i64.const 0))
  (global $cf (mut i32) (i32.const 0))
  (global $pf (mut i32) (i32.const 0))
  (global $af (mut i32) (i32.const 0))
  (global $zf (mut i32) (i32.const 0))
  (global $sf (mut i32) (i32.const 0))
  (global $of (mut i32) (i32.const 0))
  (global $df (mut i32) (i32.const 0))
  (func $fset6 (param $c i32) (param $p i32) (param $a i32) (param $z i32) (param $s i32) (param $o i32)
    (requires (∀ k ∈ [17, 18, 19, 20, 21, 22], (globalVal σ mi k).isSome))
    (ensures (σ' = setGlobalIdx (setGlobalIdx (setGlobalIdx (setGlobalIdx (setGlobalIdx (setGlobalIdx σ mi 17 (Val.i32 c)) mi 18 (Val.i32 p)) mi 19 (Val.i32 a)) mi 20 (Val.i32 z)) mi 21 (Val.i32 s)) mi 22 (Val.i32 o)))
    (global.set $cf (local.get $c)) (global.set $pf (local.get $p)) (global.set $af (local.get $a))
    (global.set $zf (local.get $z)) (global.set $sf (local.get $s)) (global.set $of (local.get $o)))
)"#

end Silmaril.Wasm.Examples.WatSpecSt
