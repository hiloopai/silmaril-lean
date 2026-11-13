module

public import Silmaril.Wasm.LimeCompile.Direct.Defs

/-!
# The direct 3.0 → Lime compiler with tail calls: definitions

Lime1 has no tail calls. The direct translation rewrites them to a call followed by a `return`:

  `return_call x` ⟶ `call x; return`,
  `return_call_indirect t y` ⟶ `call_indirect t y; return`,

**outside `try_table` bodies only**. Under a `try_table` the rewrite is wrong: the source leaves
the handler before the callee runs (`return_call_ref` bubbles out of `HANDLER`), the rewrite
does not, so an exception thrown by the callee is caught only in the rewrite (refuted in
`Silmaril.Wasm.LimeCompile.TailCex`). A `try_table` body is therefore left unchanged; the
compiler then rejects the module anyway, since `try_table` is not Lime1.

* `tailI`, `tailL`: the rewrite (an instruction becomes a sequence), recursively in every
  `block`, `loop` and `if` body, not inside `try_table`;
* `naiveI`, `naiveL`: the naive rewrite, which also rewrites inside `try_table` (refuted);
* `tailFunc`, `tailModule`: the rewrite of every function body;
* `tailCount`: the number of tail calls the rewrite replaces (size data);
* `lower m`: the select lowering of `Direct` followed by the tail rewrite;
* **`compile m : Option Lime1.Module`**: lower, check the element types, read back as Lime1.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.Tail

open Silmaril.Wasm

set_option linter.unusedTactic false in
mutual
/-- **The tail-call rewrite of one instruction** (into a sequence). -/
def tailI : Instr → List Instr
  | .returnCall x => [.call x, .return_]
  | .returnCallIndirect t y => [.callIndirect t y, .return_]
  | .block bt b => [.block bt (tailL b)]
  | .loop bt b => [.loop bt (tailL b)]
  | .if_ bt b₁ b₂ => [.if_ bt (tailL b₁) (tailL b₂)]
  | i => [i]
termination_by i => sizeOf i
decreasing_by all_goals simp_wf; all_goals omega

/-- The tail-call rewrite of an instruction sequence. -/
def tailL : List Instr → List Instr
  | [] => []
  | i :: is => tailI i ++ tailL is
termination_by is => sizeOf is
decreasing_by all_goals simp_wf; all_goals omega
end

set_option linter.unusedTactic false in
mutual
/-- **The naive rewrite**: the same, but also inside `try_table` bodies (refuted). -/
def naiveI : Instr → List Instr
  | .returnCall x => [.call x, .return_]
  | .returnCallIndirect t y => [.callIndirect t y, .return_]
  | .block bt b => [.block bt (naiveL b)]
  | .loop bt b => [.loop bt (naiveL b)]
  | .if_ bt b₁ b₂ => [.if_ bt (naiveL b₁) (naiveL b₂)]
  | .tryTable bt cs b => [.tryTable bt cs (naiveL b)]
  | i => [i]
termination_by i => sizeOf i
decreasing_by all_goals simp_wf; all_goals omega

/-- The naive rewrite of an instruction sequence. -/
def naiveL : List Instr → List Instr
  | [] => []
  | i :: is => naiveI i ++ naiveL is
termination_by is => sizeOf is
decreasing_by all_goals simp_wf; all_goals omega
end

set_option linter.unusedTactic false in
mutual
/-- The number of tail calls the rewrite replaces in an instruction. -/
def tailCountI : Instr → Nat
  | .returnCall _ => 1
  | .returnCallIndirect _ _ => 1
  | .block _ b => tailCountL b
  | .loop _ b => tailCountL b
  | .if_ _ b₁ b₂ => tailCountL b₁ + tailCountL b₂
  | _ => 0
termination_by i => sizeOf i
decreasing_by all_goals simp_wf; all_goals omega

/-- The number of tail calls the rewrite replaces in a sequence. -/
def tailCountL : List Instr → Nat
  | [] => 0
  | i :: is => tailCountI i + tailCountL is
termination_by is => sizeOf is
decreasing_by all_goals simp_wf; all_goals omega
end

/-- The tail-call rewrite of a function: its body. -/
def tailFunc (f : Func) : Func := { f with body := tailL f.body }

/-- **The tail-call rewrite of a module**: every function body; nothing else changes. -/
def tailModule (m : Module) : Module := { m with funcs := m.funcs.map tailFunc }

/-- The naive rewrite of a module. -/
def naiveModule (m : Module) : Module :=
  { m with funcs := m.funcs.map fun f => { f with body := naiveL f.body } }

/-- The lowering: typed `select`s at number types (`Direct.lowerModule`), then tail calls. -/
def lower (m : Module) : Module := tailModule (Direct.lowerModule m)

/-- **The direct compiler with tail calls**: lower, check element types, read back as Lime1. -/
def compile (m : Module) : Option Lime1.Module :=
  if Direct.funcrefElemsB (lower m) then Lime1.Module.ofCore? (lower m) else none

end Silmaril.Wasm.LimeCompile.Tail
