module

public import SysVTvExample
public import Silmaril.Project.Shapes.SysV.Rtl.Defs
public meta import Silmaril.Project.Shapes.SysV.Rtl.Defs

/-!
# Worked example, continued: `max2` lifted to RTL and to SSA-form RTL

Each build of `max2` (`SysVTvExample`) gets its own lifting rows against the machine RTL of
`Silmaril.Machine.RTL`, in both of its forms; the IR functions are written here by hand (the
lifter that would produce them from the machine code is not part of this release):

* `max2Rtl`: `r2 := (r0 >s r1)` at 32 bits; `if r2 then ret r0 else ret r1`;
* `max2SSA`: the same as SSA-form RTL, an entry block with parameters `r0`, `r1` branching to
  two return blocks; its well-formedness is decided.

| row | shape | verdict |
|---|---|---|
| `silmaril.sysv_tv.max2.{o0,o2}.lifts_rtl` | `sysv.lifts.open9`, IR `rtl Nat` | open (`Task.lifts_rtl_o0`, `Task.lifts_rtl_o2`) |
| `silmaril.sysv_tv.max2.o2.lifts_ssa` | `sysv.lifts.open9`, IR `rtlSSA Nat` | open (`Task.lifts_ssa_o2`) |
| `silmaril.sysv_tv.max2.rtl.ir_refines`, `….ssa.ir_refines` | `c.ir_refines` | open (`Task.rtl_ir_refines`, `Task.ssa_ir_refines`) |

One IR-to-C row serves both builds: `compiles_to_of_rtl` gives each build's `c.compiles_to`
row from that build's lift and the shared correspondence. The RTL functions are run on sample
arguments by compiled evaluation below (`#guard`).
-/

namespace SysVTvRtl

open Silmaril.Project.Shapes.SysV
open Silmaril.Machine

@[expose] public section

/-- `max2` in RTL: registers are numbers; `r0`, `r1` the parameters. -/
def max2Prog : RTL.Prog Nat :=
  ⟨[{ sig := ⟨2, 1⟩, params := [0, 1], entry := 0,
      code := [.binary (.cmp32 .gts) 2 0 1 1, .cond 2 2 3, .ret [0], .ret [1]] }]⟩

/-- The RTL lift of `max2` (function 0 of `max2Prog`). -/
def max2Rtl : (rtl Nat).Fn := ⟨SysVTvExample.sig, max2Prog, 0⟩

/-- `max2` in SSA-form RTL: block 0 takes `r0`, `r1`, compares and branches to the return
blocks 1 and 2. -/
def max2SSAProg : RTL.SSA.Prog Nat :=
  ⟨[{ sig := ⟨2, 1⟩, entry := 0,
      blocks := [⟨[0, 1], [.binary (.cmp32 .gts) 2 0 1], .cond 2 1 [] 2 []⟩,
        ⟨[], [], .ret [0]⟩, ⟨[], [], .ret [1]⟩] }]⟩

theorem max2SSA_wellFormed : ∀ F, max2SSAProg.func? 0 = some F → F.WellFormed := by
  intro F h
  simp only [max2SSAProg, RTL.SSA.Prog.func?, List.getElem?_cons_zero, Option.some.injEq] at h
  subst h; decide

/-- The SSA-form RTL lift of `max2`. -/
def max2SSA : (rtlSSA Nat).Fn := ⟨SysVTvExample.sig, max2SSAProg, 0, max2SSA_wellFormed⟩

/-- An empty memory (the functions touch none). -/
def mem0 : Lir.Memory := ⟨0, fun _ => 0⟩

-- `max2 3 5 = 5`, `max2 (-1) (-7) = -1` (as 32-bit words), in both IRs.
#guard (max2Prog.runMain 16 0 [3, 5] mem0).returnedValues? == some [5]
#guard (max2Prog.runMain 16 0 [0xffffffff, 0xfffffff9] mem0).returnedValues? == some [0xffffffff]
#guard (max2SSAProg.runMain 16 0 [3, 5] mem0).returnedValues? == some [5]
#guard (max2SSAProg.runMain 16 0 [0xffffffff, 0xfffffff9] mem0).returnedValues? == some [0xffffffff]

end

end SysVTvRtl

silmaril instance silmaril.sysv_tv.max2.o0.lifts_rtl := silmaril.shapes.sysv.lifts.open9
  (p := SysVTvExample.O0.placement) (frame := 16) (I := Silmaril.Project.Shapes.SysV.rtl Nat)
  (f := SysVTvRtl.max2Rtl)
silmaril instance silmaril.sysv_tv.max2.o2.lifts_rtl := silmaril.shapes.sysv.lifts.open9
  (p := SysVTvExample.O2.placement) (frame := 0) (I := Silmaril.Project.Shapes.SysV.rtl Nat)
  (f := SysVTvRtl.max2Rtl)
silmaril instance silmaril.sysv_tv.max2.o2.lifts_ssa := silmaril.shapes.sysv.lifts.open9
  (p := SysVTvExample.O2.placement) (frame := 0) (I := Silmaril.Project.Shapes.SysV.rtlSSA Nat)
  (f := SysVTvRtl.max2SSA)
silmaril instance silmaril.sysv_tv.max2.rtl.ir_refines := silmaril.shapes.c.ir_refines
  (I := Silmaril.Project.Shapes.SysV.rtl Nat) (f := SysVTvRtl.max2Rtl) (F := SysVTvExample.cfn)
silmaril instance silmaril.sysv_tv.max2.ssa.ir_refines := silmaril.shapes.c.ir_refines
  (I := Silmaril.Project.Shapes.SysV.rtlSSA Nat) (f := SysVTvRtl.max2SSA) (F := SysVTvExample.cfn)

namespace SysVTvRtl

/-! ## Open rows, frozen as `Task` statements, and what they give -/

@[expose] public def Task.lifts_rtl_o0 : Prop := silmaril.sysv_tv.max2.o0.lifts_rtl
@[expose] public def Task.lifts_rtl_o2 : Prop := silmaril.sysv_tv.max2.o2.lifts_rtl
@[expose] public def Task.lifts_ssa_o2 : Prop := silmaril.sysv_tv.max2.o2.lifts_ssa
@[expose] public def Task.rtl_ir_refines : Prop := silmaril.sysv_tv.max2.rtl.ir_refines
@[expose] public def Task.ssa_ir_refines : Prop := silmaril.sysv_tv.max2.ssa.ir_refines

/-- **Both builds through one RTL function**: the two lifts and the one correspondence give
the two-build row. -/
public theorem builds_of_rtl (h0 : Task.lifts_rtl_o0) (h2 : Task.lifts_rtl_o2)
    (hr : Task.rtl_ir_refines) : silmaril.sysv_tv.max2.builds :=
  SysVTvExample.builds_of (Silmaril.Project.Shapes.C.CompilesTo.of_lift h0 hr)
    (Silmaril.Project.Shapes.C.CompilesTo.of_lift h2 hr)

/-- **The `-O2` row through the SSA-form lift.** -/
public theorem o2_compiles_to_of_ssa (h : Task.lifts_ssa_o2) (hr : Task.ssa_ir_refines) :
    silmaril.sysv_tv.max2.o2.compiles_to :=
  Silmaril.Project.Shapes.C.CompilesTo.of_lift h hr

end SysVTvRtl
