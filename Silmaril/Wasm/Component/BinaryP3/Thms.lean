module

public import Silmaril.Wasm.Component.BinaryP3.Encode.Defs
public import Silmaril.Proofs.Wasm.Component.BinaryP3.RoundTrip
public import Silmaril.Proofs.Wasm.Component.BinaryP3.Conservative

/-!
# Component binaries with async built-ins: verified parsing

Proofs in `Silmaril.Proofs.Wasm.Component.BinaryP3.{RoundTrip,Conservative}`, the laws of
`Silmaril.Wasm.Component.Binary.Thms` for the extended syntax:

* `parse_sound : parse b = .ok c → (componentG (b.size + 1)).G b.data.toList c`;
* `parse_encode : encode c = some b → parse b = .ok c` (the encoder fails only on
  numbers or lengths of `2 ^ 32` or more);
* `componentG_functional`: the grammar is unambiguous;
* `encode_ofV0 : encode (Ast.ofV0 c) = Binary.encode c` and
  `parse_encode_ofV0 : Binary.encode c = some b → parse b = .ok (Ast.ofV0 c)`: on the
  bytes the old encoder writes, the new parser returns the embedded old syntax;
* `parse_ofV0 : Binary.parse b = .ok c → parse b = .ok (Ast.ofV0 c)` (conservativity on
  every input: the new grammar includes the old one, `Conservative.component_incl`).

Every canonical built-in of `Binary.md` at `d095e2f` has a constructor of `Canon`, a
production of `canonG` and a case of `Encode.canon`; `RoundTrip.canon_G` covers them all.
-/
