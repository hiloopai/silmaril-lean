module

public import Silmaril.Machine.X86.Lir.Defs

/-! # A tabulated layout for the x86-64 backend

`X86.Backend.layout A p codeBase` defines the address of every function and block by
prefix sums over the encoded program (`funcOff`, `blockOff`), recomputed at every query:
`encodeAt` queries it once per jump and call, so `X86.Backend.compile` is quadratic in
the code size, with every instruction re-encoded each time (about 10 s for a csmith
program). `fastLayout` computes the same sums once, in arrays, and `compile` is
`X86.Backend.compile` with that layout: the same `progErrors` check, the same
`progCode`, the same `encodeAt`.

## Intended theorem

`(fastLayout A p c).func g = (layout A p c).func g` for every `g < p.funcs.length`, and
`(fastLayout A p c).block f l = (layout A p c).block f l` for every existing block
(out-of-range queries fall back to `layout` itself), hence
`compile A p c = X86.Backend.compile A p c`: the bytes are those of the verified
backend, and `X86.Backend.compile_refines` applies to them. The evaluator freezes this
file.
-/

@[expose] public section

namespace Silmaril.Compile.Target

open Silmaril.Machine
open Silmaril.X86.Backend

variable {P : Type} (A : Assign P)

/-- `funcOff` and `blockOff` of every function and block, computed once. -/
def fastLayout (p : Lir.Prog P) (codeBase : Nat) : Layout :=
  let slow := layout A p codeBase
  let (funcOffs, blockOffs, _) := p.funcs.zipIdx.foldl
    (fun (fo, bo, off) (fn, f) =>
      let pro := lenOf (prologue A f fn)
      let (offs, _) := fn.blocks.foldl
        (fun (os, o) b => (os.push o, o + lenOf (blockCode A f (nslots fn) b))) (#[], pro)
      (fo.push off, bo.push offs, off + lenOf (funcCode A f fn)))
    ((#[] : Array Nat), (#[] : Array (Array Nat)), 0)
  { func := fun g => match funcOffs[g]? with
      | some o => codeBase + o
      | none => slow.func g
    block := fun f l => match funcOffs[f]?, (blockOffs[f]?).bind (·[l]?) with
      | some fo, some bo => codeBase + fo + bo
      | _, _ => slow.block f l }

/-- `X86.Backend.compile` with `fastLayout`. -/
def compileX86Fast (p : Lir.Prog P) (codeBase : Nat) : Except (List Error) Image :=
  match progErrors A p with
  | [] =>
    let L := fastLayout A p codeBase
    .ok ⟨encodeAt L codeBase (progCode A p), L⟩
  | errs => .error errs

end Silmaril.Compile.Target
