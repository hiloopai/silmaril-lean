module

public import Silmaril.Compiler.Core.Spec.Defs
public import Silmaril.Compiler.Forks.CoreComp.Target.Runtime.Defs
public import Silmaril.Compiler.Target.RegAlloc.Defs
public import Silmaril.Compiler.Target.X86LayoutCorrect.Defs

/-! # From linked Lir to an artifact

`artifactOf l` runs the proved Lir pipeline on a linked program (`Lir.Alloc.spill` with
`firstK 7`, then `X86.Backend.compile`) at the code address `codeBase`, and packages the
result as a `Spec.Artifact`: the code, the address of `__ccomp_start`, the stack-check
sites (`X86.Backend.stackSites`) and the initial image of the linear memory. It is the
last stage of `Verified.compile`; its correctness is `Verified.artifactOf_sound`
(`Silmaril/Compile/Core/Verified/Backend.lean`), from `Lir.Alloc.spill_refines` and
`X86.Backend.compile_refines`.

Unlike the Ail route, it does not renumber registers by liveness first
(`Target.RegAlloc.renumber` is unproved). It requires `__ccomp_start` to take the two
startup arguments (`argc`, `argv`), and refuses a link with a stack-check site needing
more than `Spec.maxStackNeed` bytes (the observation caps the requirement there, so such
a check could not count as exhaustion).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Backend

open Silmaril.Machine
open Spec

/-- Where the verified route links its code (above the default ELF segments, below the
linear memory and stack that crt0 maps). -/
def codeBase : Nat := 0x10000000

/-- The Lir program the backend compiles: the link spilled with `firstK 7`. -/
def lower (l : Mir.Linked) : Lir.Prog (Fin 9) := Lir.Alloc.spill (Lir.Alloc.firstK 7) l.prog

/-- The register assignment of the backend. -/
def assign : X86.Backend.Assign (Fin 9) := X86.Backend.Assign.fin 9 (by decide)

def artifactOf (l : Mir.Linked) : Except String Artifact :=
  match X86.Backend.compile assign (lower l) codeBase with
  | .error es => .error s!"x86-64 backend: {repr (es.take 5)}"
  | .ok img =>
    match l.funcs[Silmaril.Compile.Forks.CoreComp.Target.startSymbol]? with
    | none => .error "no __ccomp_start"
    | some start =>
      if l.data[Silmaril.Compile.Forks.CoreComp.Target.ctlSymbol]? != some ctlAddr then .error "control block not at ctlAddr"
      else if !(l.prog.funcs[start]?.any (·.params.length == 2)) then .error "__ccomp_start must take argc and argv"
      else if !(X86.Backend.stackSites (lower l) img.layout).all (·.2 ≤ maxStackNeed) then
        .error "a function needs more than maxStackNeed bytes of stack"
      else .ok { codeBase, code := img.code, entry := img.layout.func start,
                 stackSites := X86.Backend.stackSites (lower l) img.layout,
                 memSize := Silmaril.Compile.Forks.CoreComp.Target.memSize, imageBase := l.dataBase, image := l.image,
                 argBase := Silmaril.Compile.Forks.CoreComp.Target.argBase, argSize := Silmaril.Compile.Forks.CoreComp.Target.argSize }

end Silmaril.Compile.Core.Backend
