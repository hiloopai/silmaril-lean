module

public import Silmaril.Raw.Machine.X86.Linking.Relocation

/-! Small satisfiable AST cases isolate resolution/layout failures from parser
cost. `Fixture` separately checks complete real compiler/linker byte inputs. -/

@[expose] public section

namespace Silmaril.X86.Linking.Checks

open Formats.ELF Formats.ELF.Link Relocation

def header : Header := ⟨0, 0, 1, 62, 1, 0, 0, 0, 0, 64, 0, 0, 64, 2, 0⟩
def nullPart : ObjectSection := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, [], #[]⟩
def callerPart : ObjectSection := ⟨⟨0, 1, 6, 0, 0, 4, 0, 0, 4, 0⟩, [], #[0, 0, 0, 0]⟩
def calleePart : ObjectSection := ⟨⟨0, 1, 6, 0, 0, 1, 0, 0, 1, 0⟩, [], #[0x90]⟩
def nullSymbol : ObjectSymbol := ⟨⟨0, 0, 0, 0, 0, 0⟩, []⟩
def undefined : ObjectSymbol := ⟨⟨0, 16, 0, 0, 0, 0⟩, [102]⟩
def defined : ObjectSymbol := ⟨⟨0, 18, 0, 1, 0, 1⟩, [102]⟩
def caller : ObjectFile := ⟨header, [nullPart, callerPart], [nullSymbol, undefined], [⟨1, 0, 1, 2, 0⟩]⟩
def callee : ObjectFile := ⟨header, [nullPart, calleePart], [nullSymbol, defined], []⟩
def layout : Layout := [⟨⟨0, 1⟩, 0x1000⟩, ⟨⟨1, 1⟩, 0x1020⟩]

/-- Nonvacuity: the same ASTs used in the failure checks do successfully link. -/
theorem succeeds : Relocation.link [caller, callee] layout = some
    [⟨⟨0, 1⟩, 0x1000, 6, 4, #[0x20, 0, 0, 0]⟩,
     ⟨⟨1, 1⟩, 0x1020, 6, 1, #[0x90]⟩] := by rfl

theorem unresolved : Relocation.link [caller] [⟨⟨0, 1⟩, 0x1000⟩] = none := by rfl

/-- Complete, disjoint placement does not rescue duplicate strong definitions. -/
theorem duplicate_definition : Relocation.link [caller, callee, callee]
    (layout ++ [⟨⟨2, 1⟩, 0x1040⟩]) = none := by rfl

theorem overlapping_layout : Relocation.link [caller, callee]
    [⟨⟨0, 1⟩, 0x1000⟩, ⟨⟨1, 1⟩, 0x1002⟩] = none := by rfl

theorem incomplete_layout : Relocation.link [caller, callee]
    [⟨⟨0, 1⟩, 0x1000⟩] = none := by rfl

theorem misaligned_layout : Relocation.link [caller, callee]
    [⟨⟨0, 1⟩, 0x1001⟩, ⟨⟨1, 1⟩, 0x1020⟩] = none := by rfl

theorem overlapping_patches : Relocation.link
    [{ caller with relocations := caller.relocations ++ caller.relocations }, callee]
    layout = none := by rfl

/-- Unsupported mechanisms are rejected even if no relocation references them. -/
theorem unused_weak : Relocation.link
    [{ callee with symbols := [⟨{ defined.raw with info := 34 }, defined.name⟩] }]
    [⟨⟨0, 1⟩, 0x1000⟩] = none := by rfl

theorem unused_common : Relocation.link
    [{ callee with symbols := [⟨{ defined.raw with sectionIndex := 0xfff2 }, defined.name⟩] }]
    [⟨⟨0, 1⟩, 0x1000⟩] = none := by rfl

theorem unused_ifunc : Relocation.link
    [{ callee with symbols := [⟨{ defined.raw with info := 26 }, defined.name⟩] }]
    [⟨⟨0, 1⟩, 0x1000⟩] = none := by rfl

theorem unused_tls : Relocation.link
    [{ callee with symbols := [⟨{ defined.raw with info := 22 }, defined.name⟩] }]
    [⟨⟨0, 1⟩, 0x1000⟩] = none := by rfl

theorem unused_group : Relocation.link
    [{ callee with sections := callee.sections ++
      [⟨{ nullPart.header with kind := 17 }, [], #[]⟩] }]
    [⟨⟨0, 1⟩, 0x1000⟩] = none := by rfl

end Silmaril.X86.Linking.Checks
