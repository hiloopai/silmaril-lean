module

public import Silmaril.Wasm.Component.Streams.KernelWat.Defs
public import Silmaril.Wasm.JcoTool.WatCert.Thms

/-!
# The text templates of `wasm-streams-gen`: what the printed text and the written bytes are

* `coreText_sound`, `teeText_sound`: a printed text is the template's (`KM.coreWat`, `teeWat`)
  and denotes a Core 3.0 module in silmaril's text grammar;
* `coreBytes_sound`, `teeBytes_sound`: the written bytes encode, in silmaril's Core 3.0 binary
  grammar, the module that the template's text denotes;
* `core_same`, `tee_same`: text and bytes denote one module.

Translation validation per output (`WatCert.certify_sound`), not a proof about the templates.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.KernelWat

open Silmaril.Wasm
open Silmaril.Wasm.Component.Streams.Kernel
open Silmaril.Wasm.JcoTool.WatCert

theorem coreText_sound {name : String} {k : KM} {batch wmax : Nat} {t : String}
    (h : coreText name k batch wmax = .ok t) :
    t = KM.coreWat name k (clampBatch batch) wmax ∧ ∃ m, Text.Core.Encodes t m := by
  obtain ⟨rfl, m, _, _, hm⟩ := checkedText_sound h
  exact ⟨rfl, m, hm⟩

theorem coreBytes_sound {name : String} {k : KM} {batch wmax : Nat} {b : ByteArray}
    (h : coreBytes name k batch wmax = .ok b) :
    ∃ m, Text.Core.Encodes (KM.coreWat name k (clampBatch batch) wmax) m ∧
      Binary.Core.Encodes b.data.toList m := by
  obtain ⟨m, _, h1, h2⟩ := checkedBytes_sound h
  exact ⟨m, h1, h2⟩

theorem core_same {name : String} {k : KM} {batch wmax : Nat} {t : String} {b : ByteArray}
    (ht : coreText name k batch wmax = .ok t) (hb : coreBytes name k batch wmax = .ok b) :
    ∃ m, Text.Core.Encodes t m ∧ Binary.Core.Encodes b.data.toList m :=
  text_bytes_same ht hb

theorem teeText_sound {name : String} {batch : Nat} {t : String} (h : teeText name batch = .ok t) :
    t = teeWat name (clampBatch batch) ∧ ∃ m, Text.Core.Encodes t m := by
  obtain ⟨rfl, m, _, _, hm⟩ := checkedText_sound h
  exact ⟨rfl, m, hm⟩

theorem teeBytes_sound {name : String} {batch : Nat} {b : ByteArray}
    (h : teeBytes name batch = .ok b) :
    ∃ m, Text.Core.Encodes (teeWat name (clampBatch batch)) m ∧
      Binary.Core.Encodes b.data.toList m := by
  obtain ⟨m, _, h1, h2⟩ := checkedBytes_sound h
  exact ⟨m, h1, h2⟩

theorem tee_same {name : String} {batch : Nat} {t : String} {b : ByteArray}
    (ht : teeText name batch = .ok t) (hb : teeBytes name batch = .ok b) :
    ∃ m, Text.Core.Encodes t m ∧ Binary.Core.Encodes b.data.toList m :=
  text_bytes_same ht hb

end Silmaril.Wasm.Component.Streams.KernelWat
