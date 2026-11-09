module

public import Silmaril.X86.SegVC9.Thms

/-!
# `seg_vc9`: a worked segment on the open machine over `Ext9`

The two instructions

```
69 c0 01 01 01 01    imul $0x1010101, %eax, %eax     (an Ext9 form)
89 c2                mov  %eax, %edx                 (an Ext form)
```

(the byte-summing step of a `popcount32`) as an `Open9.isa` segment from offset 0 to the
exit at offset 8. The listing is checked against `Open9.decode` by `decide`; `seg_vc9`
unfolds the segment VC through both instructions, and `seg_runsIn9` turns it into a run
inside the code.
-/

@[expose] public section

namespace Silmaril.X86.SegVC9.Examples

open Silmaril.X86 (MState Word Byte)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86.SegVC
open Silmaril.X86.FnContract (RunsIn InCode)

/-- `imul $0x1010101, %eax, %eax; mov %eax, %edx`. -/
def code : List Byte := [0x69, 0xc0, 0x01, 0x01, 0x01, 0x01, 0x89, 0xc2]

/-- The listing of `code`. -/
def listing : Listing Open9.isa :=
  [(0, .new (.imulI .d .rax (.reg .rax) 0x01010101), 6),
   (6, .ext8 (.base (.mov .d (.reg .rdx) .rax)), 2)]

theorem listing_valid : listing.valid Open9.isa code = true := by decide

/-- The exit's postcondition: `edx` holds `x * 0x01010101` (zero-extended). -/
def post (x : BitVec 32) (t : MState) : Prop :=
  t.core.read .rdx = (x * 0x01010101#32).setWidth 64

/-- **The segment VC**, proved by `seg_vc9`. -/
theorem vc (base : Word) (x : BitVec 32) (s : MState)
    (hrip : s.core.rip = base + BitVec.ofNat 64 0) (hl : Loaded s.memory base code)
    (hx : (s.core.read .rax).setWidth 32 = x) :
    wpN Open9.isa code listing [] (segStops [8] (post x)) [] [] base none 2 0 s := by
  seg_vc9 [listing, segStops, List.map_cons, List.map_nil, nextAt, post, hrip, hl, hx]
  -- left: the product, with the immediate as `16843009#32` on one side and `0x01010101#32` on
  -- the other (equal by `rfl`)
  rfl

/-- The same segment VC by `seg_vc9_var` (the simp sets, with the listing passed directly). -/
theorem vc_var (base : Word) (x : BitVec 32) (s : MState)
    (hrip : s.core.rip = base + BitVec.ofNat 64 0) (hl : Loaded s.memory base code)
    (hx : (s.core.read .rax).setWidth 32 = x) :
    wpN Open9.isa code listing [] (segStops [8] (post x)) [] [] base none 2 0 s := by
  seg_vc9_var [listing, segStops, List.map_cons, List.map_nil, nextAt, post, hrip, hl, hx]
  rfl

/-- **The segment runs inside the code** to a state with `edx = x * 0x01010101`. -/
theorem runs (base : Word) (x : BitVec 32) (s : MState)
    (hrip : s.core.rip = base + BitVec.ofNat 64 0) (hl : Loaded s.memory base code)
    (hx : (s.core.read .rax).setWidth 32 = x) :
    ∃ t, RunsIn Open9.isa (InCode Open9.isa base code.length) s t ∧
      t.core.read .rdx = (x * 0x01010101#32).setWidth 64 :=
  seg_runsIn9 listing_valid (vc base x s hrip hl hx) hl hrip

end Silmaril.X86.SegVC9.Examples
