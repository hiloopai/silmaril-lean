module

public import Batteries.Data.Except
public import Silmaril.X86.Assembly.Notation.Defs
public import Silmaril.X86.Verify.Program.Defs
/-! # Checking assembly text against a program

`ParsesAssembly` relates a literal assembly string to the existing instruction
terms. It does not assert that an arbitrary ELF implements that string. A separate
`Program.SourceCertificate` connects those same terms, addresses and lengths to
binary bytes. Both obligations can be checked by Lean without trusting the
assembly macro, exporter, or Rust generator.
-/

@[expose] public section

namespace Silmaril.X86.Verify

/-- The ordinary assembly parser returns exactly the represented instruction
terms. Addresses and consumed byte lengths belong to the separate source
certificate, since this assembly notation uses relative displacements. -/
def Program.ParsesAssembly (program : Program) (source : String) : Prop :=
  X86.Assembly.parse source = .ok (program.instructions.toList.map (·.instr))

instance (program : Program) (source : String) : Decidable (program.ParsesAssembly source) :=
  inferInstanceAs (Decidable (_ = _))

/-- Once checked, the assembly text and the binary source decoder agree on the
instruction terms. This composes existing certificates; it adds no ISA semantics. -/
theorem Program.ParsesAssembly.decode {program : Program} {source : String}
    {region : Decompile.Region} {fuel : Nat}
    (assembly : program.ParsesAssembly source)
    (binary : program.SourceCertificate region fuel) :
    (region.decode? fuel).map (List.map Decompile.Decoded.instr) =
      (X86.Assembly.parse source).toOption := by
  unfold Program.ParsesAssembly at assembly
  rw [binary.2, assembly]
  rfl

end Silmaril.X86.Verify
