module

public import Silmaril.Wasi.Versions.HttpHdrOver.Defs
public import Silmaril.Wasi.Versions.HttpHdr.Thms

@[expose] public section

/-!
# HTTP headers of requests and responses across versions: theorems

PROVED (standard axioms):

* `fwdHdr_model`: for every sound table, over every host of the imported headers theory, the
  forwarding composite is a model of the exported one (invariant: equal theory states).
* **`hdr2Over3_model`**, **`hdr3Over2_model`**: the two instances.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- **The invariant of a forwarding adapter**: the two theory states are equal. -/
theorem fwdHdr_inv {N N' : HdrFns} {P : List (FnName × FnName)} (hP : HTabOk N N' P) :
    WpInv (fwdHdr N N' P hP) () (hdrTh N') (hdrTh N) (fun _ q' q => q = q') where
  init := rfl
  call := by
    intro _ q' q c hJ r q'' hs
    obtain ⟨hs1, hs2⟩ := hTabOk_find hP c.1.2
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hs1
    refine ⟨q'', ?_, rfl⟩
    have hs' := hs
    rw [hdrTh_step N' (hs2.trans ho)] at hs'
    show (hdrTh N).step q (.imp c.1.1 c.2 r) = some q''
    rw [hdrTh_step N ho, hJ]
    exact hs'

/-- **A forwarding adapter of a sound table**: over every host of `hdrTh N'`, the composite is
a model of `hdrTh N`. -/
theorem fwdHdr_model {N N' : HdrFns} {P : List (FnName × FnName)} (hP : HTabOk N N' P)
    {Y : Sig.{0}} {η : Host Y N'.fns} (hη : (hostSat (hdrTh N').Accepts).holds η) :
    (hostSat (hdrTh N).Accepts).holds (link η (ofSBody (fwdHdr N N' P hP) ())) :=
  link_model (ag_of_wpInv (fwdHdr_inv hP)) hη

/-- **Headers, 0.2 over 0.3**: over every host of the 0.3 headers theory, the composite is a
model of the 0.2 one. -/
theorem hdr2Over3_model {Y : Sig.{0}} {η : Host Y hdrFns3.fns}
    (hη : (hostSat (hdrTh hdrFns3).Accepts).holds η) :
    (hostSat (hdrTh hdrFns2).Accepts).holds (link η (ofSBody hdr2Over3 ())) :=
  fwdHdr_model hTab23_ok hη

/-- **Headers, 0.3 over 0.2**: over every host of the 0.2 headers theory, the composite is a
model of the 0.3 one. -/
theorem hdr3Over2_model {Y : Sig.{0}} {η : Host Y hdrFns2.fns}
    (hη : (hostSat (hdrTh hdrFns2).Accepts).holds η) :
    (hostSat (hdrTh hdrFns3).Accepts).holds (link η (ofSBody hdr3Over2 ())) :=
  fwdHdr_model hTab32_ok hη

end Silmaril.Wasi.Versions.Net
