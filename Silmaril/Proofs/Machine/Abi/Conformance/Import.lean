module

public import Silmaril.Machine.Abi.Conformance.Import.Defs
import Silmaril.Data.Layout.Header.Import.Thms

/-! Proofs for `Silmaril.Machine.Abi.Conformance.Import.Thms`. -/

public section

namespace Silmaril.Proofs.Machine.Abi.Conformance.Import

open Silmaril.Machine.Abi.Conformance
open Silmaril.Data.Layout.Header.Import

theorem declares_iff_of_header {A : AbiDef} {hdr : HeaderSrc} {ccs : List CallConv}
    {imp : Imported} {f : String} {p : A.V.Proto}
    (h : (Silmaril.Data.Layout.Header.read hdr.files hdr.root).toOption = some imp.header)
    (hcc : ccsOk ccs imp = true) :
    Declares A hdr f p ↔ DeclaresImport A ccs imp f p := by
  unfold Declares DeclaresImport HeaderSrc.proto? Imported.proto?
  rw [h]
  simp only [Option.bind_some]
  constructor
  · rintro ⟨cp, hp, hl⟩
    have hn := Silmaril.Data.Layout.Header.Import.mem_names_of_proto hp
    exact ⟨cp, hp, List.all_eq_true.mp hcc f hn, hl⟩
  · rintro ⟨cp, hp, _, hl⟩
    exact ⟨cp, hp, hl⟩

theorem declares_iff_of_proto {A : AbiDef} {hdr : HeaderSrc} {ccs : List CallConv}
    {imp : Imported} {f : String} {p : A.V.Proto} (h : hdr.proto? f = imp.proto? f)
    (hcc : (imp.fn? f).any (fun x => ccs.contains x.2.cc) = true) :
    Declares A hdr f p ↔ DeclaresImport A ccs imp f p := by
  simp only [Declares, DeclaresImport, h, hcc, true_and]

/-- The routes agree on the prototype and the convention of every name of `fs`. -/
theorem declares_iff_of_all {A : AbiDef} {hdr : HeaderSrc} {ccs : List CallConv}
    {imp : Imported} {fs : List String}
    (h : fs.all (fun f => hdr.proto? f == imp.proto? f &&
      (imp.fn? f).any (fun x => ccs.contains x.2.cc)) = true) :
    ∀ f ∈ fs, ∀ p : A.V.Proto, Declares A hdr f p ↔ DeclaresImport A ccs imp f p := by
  intro f hf p
  have hf' := List.all_eq_true.mp h f hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hf'
  exact declares_iff_of_proto hf'.1 hf'.2

end Silmaril.Proofs.Machine.Abi.Conformance.Import

end
