module

public import Silmaril.Wasm.Binaryen.Toolkit.AsSound
public import Silmaril.Wasm.Binaryen.Toolkit.DisassembleSound

@[expose] public section

/-! # Exact module preservation across successful text/binary tool round trips

Binary and text grammar functionality identify the retained AST. No byte
identity, source formatting preservation, or acceptance-completeness premise is
asserted: each call must actually succeed on its supported text/binary surface.
-/

namespace Silmaril.Wasm.Binaryen.Toolkit

/-- Disassembling an assembled binary retains the exact original parsed module. -/
theorem disassemble_assembled_module {input : String} {assembled : AssembledArtifact}
    {disassembled : DisassembledArtifact}
    (ha : assembleText input = .ok assembled)
    (hd : disassembleBytes assembled.bytes = .ok disassembled) :
    disassembled.module = assembled.module :=
  Binary.Core.functional (disassembleBytes_sound hd).1 (assembleText_sound ha).2.2

/-- Reassembling disassembled text retains the exact original decoded module. -/
theorem assemble_disassembled_module {input : ByteArray} {disassembled : DisassembledArtifact}
    {assembled : AssembledArtifact}
    (hd : disassembleBytes input = .ok disassembled)
    (ha : assembleText disassembled.text = .ok assembled) :
    assembled.module = disassembled.module :=
  Text.Core.encodes_functional (assembleText_sound ha).1 (disassembleBytes_sound hd).2

/-- The original and reassembled bytes encode the same retained module, even
when binary encoding or custom sections differ. -/
theorem disassemble_assemble_binary {input : ByteArray} {disassembled : DisassembledArtifact}
    {assembled : AssembledArtifact}
    (hd : disassembleBytes input = .ok disassembled)
    (ha : assembleText disassembled.text = .ok assembled) :
    Binary.Core.Encodes input.data.toList disassembled.module ∧
      Binary.Core.Encodes assembled.bytes.data.toList disassembled.module := by
  refine ⟨(disassembleBytes_sound hd).1, ?_⟩
  simpa only [assemble_disassembled_module hd ha] using (assembleText_sound ha).2.2

end Silmaril.Wasm.Binaryen.Toolkit
