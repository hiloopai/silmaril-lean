module

public import Silmaril.X86.Sep.SysV.Thms
import Silmaril.Proofs.X86.Sep.Examples

/-!
# A worked example: a store and a load under `∗` framing

The two instructions

```
50    push %rax      a store: [rsp - 8] := rax, rsp := rsp - 8
5b    pop  %rbx      a load:  rbx := [rsp], rsp := rsp + 8
```

copy `rax` to `rbx` through the eight stack bytes below `rsp`. `push_pop` is their triple on
every machine extending `Open.isa`: the code is returned unchanged, the stack slot (owned at
entry as `blockAny`, contents unknown) ends holding `v`, and nothing else is mentioned, so
everything else is unchanged. `push_pop_open9` is the same triple on the default machine
`Open9.isa`, and `push_pop_frame` adds a frame (a caller's buffer `bytesPt a bs` and its
callee-saved `rbp`) that the code provably leaves alone. The proofs are the instruction
triples `push_step` and `pop_step`, each framed with what the other owns, and `Triple.trans`.
-/

@[expose] public section

namespace Silmaril.X86.Sep.Examples

open Silmaril.X86 (Word Byte Reg)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep

variable {σ : Type} {I : Isa σ}

/-- **`push rax; pop rbx`** on every machine extending `Open.isa`. -/
theorem push_pop (E : Open.isa.Extends I) (pc s v : Word) (hpc : pc.toNat + 1 < 2 ^ 64)
    (hs : 8 ≤ s.toNat) :
    SPEC I (codePt pc.toNat [0x50, 0x5b])
      (ripPt pc ∗ regPt .rsp s ∗ regPt .rax v ∗ regAny .rbx ∗ blockAny (s.toNat - 8) 8)
      (ripPt (pc + 2#64) ∗ regPt .rsp s ∗ regPt .rax v ∗ regPt .rbx v ∗
        wordPt (s.toNat - 8) v) :=
  Silmaril.Proofs.X86.SepExamples.push_pop E pc s v hpc hs

/-- The same on the default machine `Open9.isa`. -/
theorem push_pop_open9 (pc s v : Word) (hpc : pc.toNat + 1 < 2 ^ 64) (hs : 8 ≤ s.toNat) :
    SPEC Open9.isa (codePt pc.toNat [0x50, 0x5b])
      (ripPt pc ∗ regPt .rsp s ∗ regPt .rax v ∗ regAny .rbx ∗ blockAny (s.toNat - 8) 8)
      (ripPt (pc + 2#64) ∗ regPt .rsp s ∗ regPt .rax v ∗ regPt .rbx v ∗
        wordPt (s.toNat - 8) v) :=
  push_pop Open9.extendsOpen pc s v hpc hs

/-- **Framing**: a caller's buffer and its `rbp` survive, by the frame rule alone. -/
theorem push_pop_frame (pc s v u : Word) (a : Nat) (bs : List Byte)
    (hpc : pc.toNat + 1 < 2 ^ 64) (hs : 8 ≤ s.toNat) :
    SPEC Open9.isa (codePt pc.toNat [0x50, 0x5b])
      ((ripPt pc ∗ regPt .rsp s ∗ regPt .rax v ∗ regAny .rbx ∗ blockAny (s.toNat - 8) 8) ∗
        bytesPt a bs ∗ regPt .rbp u)
      ((ripPt (pc + 2#64) ∗ regPt .rsp s ∗ regPt .rax v ∗ regPt .rbx v ∗
        wordPt (s.toNat - 8) v) ∗ bytesPt a bs ∗ regPt .rbp u) :=
  (push_pop_open9 pc s v hpc hs).frame _

end Silmaril.X86.Sep.Examples
