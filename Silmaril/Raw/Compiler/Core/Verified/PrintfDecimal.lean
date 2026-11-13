module

public import Silmaril.Compiler.Core.Verified.PrintfFormat.Defs
public import Silmaril.Compiler.Core.Verified.PrintLink.Defs
public import Silmaril.Compiler.Core.Verified.Locals.Defs

/-! # Agreement of Core `%d` with the proved output-buffer routine

The Core builtin reads an ordinary signed-int argument object. The Lir code
computes its decimal digits at run time. The two sides produce identical bytes,
including the sign of negative numbers and the single digit for zero.

This is a primitive-level agreement theorem. String-literal startup, the std.core
`printf_proxy`/`listFromStr` calls and recognition of C statements are separate
obligations before the fragment can be enabled in `Verified.compile`.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.PrintfDecimal

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Mem.Concrete (Pointer)
open Spec Backend

/-- A `%d` argument is read from the same concrete int slot used by the locals fragment. -/
theorem core_decimal {file : Program} {labels : Labels} {m : Mem.Concrete.State}
    {id addr n : Int} (slot : Locals.Slot m id addr n) (range : Mem.Concrete.IntRange n)
    (bt bt' : BaseType) (k : List Frame) :
    ReturnConst.Reaches file labels
      ⟨.apply (.builtin "printf")
        [.list bt [.object (.integer 37), .object (.integer 100)],
          .list bt' [.tuple [.ctype (Mem.Concrete.intType []),
            .object (.pointer (.allocated id addr))]]], k, m⟩
      ⟨.value (.loaded (.specified (.integer (toString n).length))), k,
        {m with lastUsed := some id, stdout := m.stdout ++ toString n}⟩ := by
  have hl := Mem.Concrete.load_int ⟨file.tagDefs, m.enumTypes⟩ [] slot.live slot.plain range slot.bytes
  have hf := PrintfFormat.printFormat_d ⟨file.tagDefs, m.enumTypes⟩ [] [] (by simp) (by simp)
    m {m with lastUsed := some id} [] (.allocated id addr) n hl
  simpa using PrintfFormat.builtin_of_format (file := file) (labels := labels) [37, 100]
    (by intro c hc; simp at hc; rcases hc with rfl | rfl <;> omega)
    [(Mem.Concrete.intType [], .allocated id addr)] bt bt' k m {m with lastUsed := some id}
    (toString n) (by simpa using hf)

/-- The output link renders a signed decimal exactly as the canonical Core printf does. -/
theorem render_decimal (n : Int) :
    PrintLink.render [.int n] = coreBytes (toString n) := by
  simp [PrintLink.render, PrintLink.Item.render, coreBytes]

/-- Every signed C int fits the proved run-time decimal routine. -/
theorem decimal_fits {n : Int} (range : Mem.Concrete.IntRange n) : PrintLink.Fits [.int n] := by
  rcases range with ⟨lo, hi⟩
  refine ⟨?_, ?_⟩
  · intro it hit
    simp only [List.mem_singleton] at hit
    subst it
    simp only [PrintLink.Item.small, decide_eq_true_eq]
    omega
  · norm_num [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      PrintLink.Item.room, PrintLink.outBase, ctlAddr, Silmaril.Compile.Forks.CoreComp.Target.argBase,
      Silmaril.Compile.Forks.CoreComp.Target.memSize, Silmaril.Compile.Forks.CoreComp.Target.stackSize, Silmaril.Compile.Forks.CoreComp.Target.argSize]

/-- Source and machine agree on the output bytes at the printf primitive boundary. -/
theorem machine_decimal {n : Int} (range : Mem.Concrete.IntRange n) {w : Silmaril.Machine.Lir.Word}
    {a : Artifact} (ha : artifactOf (PrintLink.link [.int n] w) = .ok a)
    {S : Silmaril.X86.Backend.Space} {exit : Silmaril.X86.Word} {E0 : Nat} (hl : Loaded a S exit E0)
    {saved : Silmaril.X86.Reg → Silmaril.X86.Word} {init : Silmaril.X86.State}
    {args : List String} {o : Obs} (hb : MachineBeh a S exit E0 saved init args o) :
    o = .exhausted ∨ o = .exit (w.toNat % 256) (coreBytes (toString n)) := by
  simpa only [render_decimal] using PrintLink.link_sound (decimal_fits range) ha hl hb

end Silmaril.Compile.Core.Verified.PrintfDecimal
