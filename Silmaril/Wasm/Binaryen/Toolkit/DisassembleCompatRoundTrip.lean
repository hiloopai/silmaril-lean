module

public import Silmaril.Wasm.Binaryen.Toolkit.AsSound
public import Silmaril.Wasm.Binaryen.Toolkit.DisassembleCompatSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

/-- Standard assembly output and compatible disassembly retain the same module. -/
theorem disassembleCompat_assembled_module {input : String} {assembled : AssembledArtifact}
    {disassembled : DisassembledArtifact}
    (ha : assembleText input = .ok assembled)
    (hd : disassembleCompatBytes assembled.bytes = .ok disassembled) :
    disassembled.module = assembled.module :=
  Binary.Core.CompactImports.functional (disassembleCompatBytes_sound hd).1
    (Binary.Core.CompactImports.of_standard (assembleText_sound ha).2.2)

/-- Reassembly of compatible disassembly retains the original complete module. -/
theorem assemble_disassembledCompat_module {input : ByteArray} {disassembled : DisassembledArtifact}
    {assembled : AssembledArtifact}
    (hd : disassembleCompatBytes input = .ok disassembled)
    (ha : assembleText disassembled.text = .ok assembled) :
    assembled.module = disassembled.module :=
  Text.Core.encodes_functional (assembleText_sound ha).1 (disassembleCompatBytes_sound hd).2

/-- Compact or standard original bytes and reassembled standard bytes encode the
same module, without a byte-identity or unconditional acceptance claim. -/
theorem disassembleCompat_assemble_binary {input : ByteArray} {disassembled : DisassembledArtifact}
    {assembled : AssembledArtifact}
    (hd : disassembleCompatBytes input = .ok disassembled)
    (ha : assembleText disassembled.text = .ok assembled) :
    Binary.Core.CompactImports.Encodes input.data.toList disassembled.module ∧
      Binary.Core.Encodes assembled.bytes.data.toList disassembled.module := by
  refine ⟨(disassembleCompatBytes_sound hd).1, ?_⟩
  simpa only [assemble_disassembledCompat_module hd ha] using (assembleText_sound ha).2.2

end Silmaril.Wasm.Binaryen.Toolkit
