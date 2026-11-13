module

public import Silmaril.Wasm.FX.Asyncify.Host.Obs.Defs
public import Silmaril.Wasm.FX.Asyncify.Tool.Sys.Defs

/-!
# The asyncify tool as an instance of the family: its programs in the kernel

The tool `wasm-asyncify` runs Core code on a frame machine (`Tool.step`), closed by a host
(`Tool.srcStep`, observing the final host state, `Tool.Obs σ`). The family's host instance runs
the handler kernel `FXAsync.sstep`, closed by a host (`Host.hsstep`). This module translates
the tool's programs into the kernel:

* **Values.** The kernel has no locals, globals or memory. A kernel value is a whole
  straight-line state `Tool.LS` (locals, operands, globals, memory), and a frame of the
  translation carries **one** value: the tool frame's locals and operands, with the globals and
  memory **threaded** through the frames (the top frame's value has the current ones; a call
  passes them to the callee and the return passes them back).
* **Straight-line instructions** (everything but `call`, `return` and `if`): `prim 1 (segOp i)`,
  the tool's own `segCore` on the value. A trap gives no value, so the next `prim 1` (every
  translated instruction starts with one, and every body ends with `finOp`) traps.
* **A call of a defined function** `f`: `prim 1 (splitOp n)` (the arguments, in parameter order,
  split off the value as a new value on top), `call f` with arity 1, and `prim 2 mergeOp` (the
  callee's operands pushed on the caller's, the callee's globals and memory kept). The callee's
  body starts with `prim 1 (enterOp nlocals)` (its locals: the arguments and zeros) and ends
  with `prim 1 finOp`.
* **A call of an import** `f`: `prim 1 (splitOp n)`, then **`suspend f 1`**, which no frame
  handles (the translation has no `resume`): a blocking call, answered by the host `kHost E H`
  (the tool's host, its answers fitted to the import's result count), then `prim 2 mergeOp`.

`toolOut` maps the kernel's host-observed outcomes (`Host.HOut`) to the tool's (`Tool.Obs σ`): a
result value's operands and the host state. `asRes` and `mapObs` present the tool's systems and
the kernel's observing machine as `FXAsync` machines over the same value type `Tool.Obs σ`, so
that the family's stuttering simulations (`SimRel`) compare them.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Bridge

open Silmaril.Wasm
open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.FX.Asyncify.Host

variable {σ : Type}

/-- A kernel value of the translation: a straight-line state of the tool's machine. -/
abbrev KV := Tool.LS

/-- A straight-line instruction on the value. -/
def segOp (i : Instr) : List KV → List KV
  | [s] =>
    match Tool.segCore i s with
    | some s' => [s']
    | none => []
  | _ => []

/-- Split `n` arguments (in parameter order) off the value: the arguments on top (as the locals
of a new value with the same globals and memory), the rest below. -/
def splitOp (n : Nat) : List KV → List KV
  | [s] =>
    if n ≤ s.ops.length then [⟨(s.ops.take n).reverse, [], s.globals, s.mem⟩, { s with ops := s.ops.drop n }]
    else []
  | _ => []

/-- After a call: the callee's operands on the caller's, the callee's globals and memory. -/
def mergeOp : List KV → List KV
  | [r, s] => [{ s with ops := r.ops ++ s.ops, globals := r.globals, mem := r.mem }]
  | _ => []

/-- The entry of a function with `nl` declared locals: the arguments, then zeros. -/
def enterOp (nl : Nat) : List KV → List KV
  | [a] => [{ a with locals := a.locals ++ List.replicate nl 0, ops := [] }]
  | _ => []

/-- The end of a body: one value, unchanged (a trap before it left none, and it traps). -/
def finOp : List KV → List KV
  | [s] => [s]
  | _ => []

/-- The arity of import `g`. -/
def impArity (E : Tool.Env) (g : Nat) : Nat := ((E.imps[g]?).map Prod.fst).getD 0

/-- The result count of import `g`. -/
def impRes (E : Tool.Env) (g : Nat) : Nat := ((E.imps[g]?).map Prod.snd).getD 0

/-- The arity of defined function `g` (function index space: imports first). -/
def fnArity (E : Tool.Env) (g : Nat) : Nat :=
  ((E.fns[g - E.imps.length]?).map Tool.FnDef.nparams).getD 0

/-- **The translation of one instruction.** -/
def trI (E : Tool.Env) (i : Instr) : List (Ins KV) :=
  match Tool.ctlOf i with
  | some (.call g) =>
    if g < E.imps.length then [.prim 1 (splitOp (impArity E g)), .suspend g 1, .prim 2 mergeOp]
    else [.prim 1 (splitOp (fnArity E g)), .call g, .prim 2 mergeOp]
  | _ => [.prim 1 (segOp i)]

/-- The translation of code. -/
def trCode (E : Tool.Env) : List Instr → List (Ins KV)
  | [] => []
  | i :: is => trI E i ++ trCode E is

/-- The translated body of a defined function. -/
def trFn (E : Tool.Env) (fn : Tool.FnDef) : List (Ins KV) :=
  .prim 1 (enterOp fn.nlocals) :: (trCode E fn.body ++ [.prim 1 finOp])

/-- **The translated program**: defined function `g` takes one value. Imports have no body
(they are reached only by `suspend`). -/
def trP (E : Tool.Env) : Prog (Ins KV) := fun g =>
  if E.imps.length ≤ g then (E.fns[g - E.imps.length]?).map fun fn => (1, trFn E fn) else none

/-- The branch test of the translation (it has no `cond`). -/
def kTest (_ : KV) : Bool := true

/-- **The tool's host as a kernel host**: a blocking call of `g` with the argument value `a` is
answered by `H` on `a`'s locals (the arguments), fitted to `g`'s result count, reversed onto
the operands (top first), with `a`'s globals and memory. -/
def kHost (E : Tool.Env) (H : Tool.Host σ) : KHost KV σ where
  answer s g p :=
    match p with
    | [.val a] =>
      ((H.answer s g a.locals).1,
        [.val ⟨[], (Tool.fit (impRes E g) (H.answer s g a.locals).2).reverse, a.globals, a.mem⟩])
    | _ => (s, [])

/-- The kernel arguments of an export call: one value, with the tool's initial (empty) globals
and zero memory. -/
def kArgs (args : List Tool.W) : List (SV KV) := [.val ⟨args, [], [], fun _ => 0⟩]

/-- A kernel outcome with its host state as a tool observation. -/
def toolOut : HOut KV σ → Tool.Obs σ
  | .done [.val r] s => .done r.ops s
  | .done _ s => .trap s
  | .trap s => .trap s

/-- A kernel behaviour, host state observed, as a tool behaviour. -/
def obsOut : Obs (HOut KV σ) → Tool.Obs σ
  | .done [.val h] => toolOut h
  | _ => .diverges

/-! ## Machines over observations -/

/-- A tool system as an `FXAsync` machine over the values `Tool.Obs σ`: a stop `o` is the result
`[val o]`. -/
def asRes {X : Type} (step : X → Tool.SRes X σ) (x : X) : Res X (Tool.Obs σ) :=
  match step x with
  | .next y => .next y
  | .stop o => .stop (.done [.val o])

/-- Map the observations of a machine whose stops are results `[val h]`. -/
def mapObs {C O O' : Type} (g : O → O') (step : C → Res C O) (x : C) : Res C O' :=
  match step x with
  | .next y => .next y
  | .stop (.done [.val h]) => .stop (.done [.val (g h)])
  | .stop _ => .stop .trap

/-- A behaviour of `asRes` as a tool behaviour. -/
def backObs : Obs (Tool.Obs σ) → Tool.Obs σ
  | .done [.val o] => o
  | _ => .diverges

/-- The image of a behaviour under `mapObs g`. -/
def Obs.mapV {O O' : Type} (g : O → O') : Obs O → Obs O'
  | .done [.val h] => .done [.val (g h)]
  | .diverges => .diverges
  | _ => .trap

/-! ## The tool's systems in the kernel -/

/-- The translated source system: the kernel closed by the tool's host, observing host states. -/
def kSrc (E : Tool.Env) (H : Tool.Host σ) : SCfg KV × σ → Res (SCfg KV × σ) (HOut KV σ) :=
  observe (hsstep (trP E) kTest (kHost E H))

/-- Instructions that the translation simulates: no `return`, no `if` (the statement form has
neither). -/
def ctlNC : Instr → Bool
  | .return_ => false
  | .if_ _ _ _ => false
  | _ => true

/-- Code without `return` and `if`. -/
def NoCtl (code : List Instr) : Prop := ∀ i ∈ code, ctlNC i = true

/-- Every body is without `return` and `if`. -/
def Straight (E : Tool.Env) : Prop := ∀ fn ∈ E.fns, NoCtl fn.body

end Silmaril.Wasm.FX.Asyncify.Bridge
