module

public import Silmaril.Data.IncludeBytes.Kernel
public import Silmaril.Prelude.Bytes.Native.Defs
public meta import Lean.Elab.Tactic

/-! # Raw bytes and kernel bytes: the native fallback

`kbytes_rel_native` is `kbytes_rel` (kernel-only, `Silmaril.Data.IncludeBytes.Kernel`), and
when that fails, `edge_decide` with `bytes.eqByteArray`: it runs natively when the trust policy
allows it and otherwise fails, since that procedure has no kernel fallback.
-/

public meta section

namespace Silmaril.IncludeBytes.Kernel

/-- `kbytes_rel`, falling back to the native procedure `bytes.eqByteArray`. -/
syntax (name := kbytesRelNative) "kbytes_rel_native" : tactic

macro_rules
  | `(tactic| kbytes_rel_native) =>
    `(tactic| first
      | kbytes_rel
      | exact KBytes.toByteArray_eq_of_eqByteArray _ _ (by edge_decide))

end Silmaril.IncludeBytes.Kernel
