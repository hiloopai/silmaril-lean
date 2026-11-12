module

public import Silmaril.Wasm.Wat

/-!
# Example modules for the asyncify tool

Core modules in the statement form of `Silmaril.Wasm.FX.Asyncify.Tool.Frag`, written in WAT
(silmaril-lean's `wat3!`). Every import is a suspending call. `wasm-asyncify example NAME`
writes their binaries; `tools/wasm-asyncify/differential.mjs` runs them under Node.

* `sleepAdd`: one suspension, `x + sleep(x)`;
* `twice`: two suspensions in one function, two imports;
* `chain`: suspensions three calls deep (`main → mid → leaf`), with suspensions in every frame;
* `multi`: an import with two arguments and two results, a function without results;
* `noSusp`: no import call at all (the pass must be the identity on behaviours);
* `fused`: runs of pure statements before and after the only call (their re-entry checks are
  fused or dropped by the elision);
* `trapAfter`: a division that traps after a suspension when the argument is `0`;
* `deep`: four frames (`main → a → b → c`), imports without arguments or results;
* `many`: six suspensions in a row through one two-argument import;
* `computedArg`: the call's argument is computed on the stack (not statement form; spilled);
* `live`: an operand live across a suspending call;
* `liveChain`: operands live across calls of defined functions and of imports with two results
  and with none;
* `rejected`: a call inside a `block` (outside both fragments).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool.Examples

def sleepAdd := wat3! r#"
(module
  (import "env" "sleep" (func $sleep (param i32) (result i32)))
  (func $main (export "main") (param i32) (result i32) (local i32)
    local.get 0
    call $sleep
    local.set 1
    local.get 1
    local.get 0
    i32.add))
"#

def twice := wat3! r#"
(module
  (import "env" "read" (func $read (param i32) (result i32)))
  (import "env" "tick" (func $tick (param i32) (result i32)))
  (func $main (export "main") (param i32 i32) (result i32) (local i32 i32)
    local.get 0
    call $read
    local.set 2
    local.get 2
    local.get 1
    i32.mul
    local.set 3
    local.get 3
    call $tick
    local.set 2
    local.get 2
    local.get 3
    i32.xor))
"#

def chain := wat3! r#"
(module
  (import "env" "io" (func $io (param i32) (result i32)))
  (func $leaf (param i32) (result i32) (local i32)
    local.get 0
    call $io
    local.set 1
    local.get 1
    i32.const 3
    i32.add)
  (func $mid (param i32) (result i32) (local i32 i32)
    local.get 0
    i32.const 1
    i32.add
    local.set 1
    local.get 1
    call $leaf
    local.set 2
    local.get 2
    call $io
    local.set 1
    local.get 1
    call $leaf
    local.set 2
    local.get 2
    local.get 1
    i32.sub)
  (func $main (export "main") (param i32) (result i32) (local i32 i32)
    local.get 0
    call $io
    local.set 1
    local.get 1
    call $mid
    local.set 2
    local.get 0
    call $mid
    local.set 1
    local.get 1
    local.get 2
    i32.add))
"#

def multi := wat3! r#"
(module
  (import "env" "divmod" (func $divmod (param i32 i32) (result i32 i32)))
  (import "env" "log" (func $log (param i32)))
  (func $report (param i32 i32) (local i32)
    local.get 0
    local.get 1
    i32.or
    local.set 2
    local.get 2
    call $log)
  (func $main (export "main") (param i32 i32) (result i32) (local i32 i32)
    local.get 0
    local.get 1
    call $divmod
    local.set 3
    local.set 2
    local.get 2
    local.get 3
    call $report
    local.get 2
    i32.const 1000
    i32.mul
    local.get 3
    i32.add))
"#

def noSusp := wat3! r#"
(module
  (func $sq (param i32) (result i32)
    local.get 0
    local.get 0
    i32.mul)
  (func $main (export "main") (param i32) (result i32) (local i32)
    local.get 0
    call $sq
    local.set 1
    local.get 1
    i32.const 1
    i32.add))
"#

def fused := wat3! r#"
(module
  (import "env" "get" (func $get (param i32) (result i32)))
  (func $main (export "main") (param i32) (result i32) (local i32 i32 i32)
    local.get 0
    i32.const 3
    i32.mul
    local.set 1
    local.get 1
    i32.const 1
    i32.add
    local.set 2
    local.get 2
    i32.const 5
    i32.xor
    local.set 1
    local.get 1
    call $get
    local.set 3
    local.get 3
    local.get 1
    i32.sub
    local.set 2
    local.get 2
    i32.const 7
    i32.rotl
    local.set 3
    local.get 3
    local.get 2
    i32.add))
"#

def trapAfter := wat3! r#"
(module
  (import "env" "read" (func $read (param i32) (result i32)))
  (func $main (export "main") (param i32) (result i32) (local i32)
    local.get 0
    call $read
    local.set 1
    local.get 1
    local.get 0
    i32.div_u))
"#

def deep := wat3! r#"
(module
  (import "env" "tick" (func $tick))
  (import "env" "now" (func $now (result i32)))
  (func $c (param i32) (result i32) (local i32)
    call $tick
    call $now
    local.set 1
    local.get 1
    local.get 0
    i32.add)
  (func $b (param i32) (result i32) (local i32)
    local.get 0
    call $c
    local.set 1
    call $tick
    local.get 1
    i32.const 2
    i32.mul)
  (func $a (param i32 i32) (result i32) (local i32)
    local.get 0
    call $b
    local.set 2
    local.get 1
    call $b
    local.set 1
    local.get 2
    local.get 1
    i32.sub)
  (func $main (export "main") (param i32) (result i32) (local i32)
    call $now
    local.set 1
    local.get 0
    local.get 1
    call $a
    local.set 0
    local.get 0))
"#

def many := wat3! r#"
(module
  (import "env" "f" (func $f (param i32 i32) (result i32)))
  (func $main (export "main") (param i32 i32) (result i32) (local i32 i32 i32)
    local.get 0
    local.get 1
    call $f
    local.set 2
    local.get 2
    local.get 0
    call $f
    local.set 3
    local.get 3
    local.get 2
    call $f
    local.set 4
    local.get 4
    local.get 3
    call $f
    local.set 2
    local.get 2
    local.get 4
    call $f
    local.set 3
    local.get 3
    local.get 2
    call $f
    local.set 4
    local.get 4))
"#

def computedArg := wat3! r#"
(module
  (import "env" "sleep" (func $sleep (param i32) (result i32)))
  (func $main (export "main") (param i32) (result i32)
    local.get 0
    i32.const 1
    i32.add
    call $sleep))
"#

def live := wat3! r#"
(module
  (import "env" "sleep" (func $sleep (param i32) (result i32)))
  (func $main (export "main") (param i32) (result i32)
    local.get 0
    local.get 0
    i32.const 1
    i32.add
    call $sleep
    i32.add))
"#

def liveChain := wat3! r#"
(module
  (import "env" "pair" (func $pair (param i32) (result i32 i32)))
  (import "env" "show" (func $show (param i32 i32)))
  (func $g (param i32) (result i32)
    local.get 0
    i32.const 10
    local.get 0
    call $pair
    i32.sub
    i32.mul
    i32.add)
  (func $main (export "main") (param i32 i32) (result i32)
    local.get 1
    local.get 0
    call $g
    local.get 1
    local.get 0
    call $show
    i32.xor
    local.get 0
    call $g
    i32.add))
"#

def rejected := wat3! r#"
(module
  (import "env" "sleep" (func $sleep (param i32) (result i32)))
  (func $main (export "main") (param i32) (result i32)
    block (result i32)
      local.get 0
      call $sleep
    end))
"#

/-- The examples by name. -/
def all : List (String × Silmaril.Wasm.Module) :=
  [("sleep-add", sleepAdd), ("twice", twice), ("chain", chain), ("multi", multi),
   ("no-susp", noSusp), ("fused", fused), ("trap-after", trapAfter), ("deep", deep),
   ("many", many), ("computed-arg", computedArg), ("live", live), ("live-chain", liveChain),
   ("rejected", rejected)]

end Silmaril.Wasm.FX.Asyncify.Tool.Examples
