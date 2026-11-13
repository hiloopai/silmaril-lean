module

public import Silmaril.Proofs.Wasi.Versions.P3OverP2.Clock
public import Silmaril.Proofs.Wasi.Versions.P3OverP2.Stdout
public import Silmaril.Proofs.Wasi.Versions.P3OverP2.Read

/-!
# Proofs: WASI 0.3 over 0.2 is an implementation morphism

`link_model` turns each guarantee of the component into a property of the composite: linked
over a 0.2 host, the component is a 0.3 host. `p3OverP2_model`: over every host of `p2ThF F`
(the loose 0.2 theory with the file contents `F`), the composite is a model of `p3Th F`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P3

variable {Y : Sig.{0}} {η : Host Y P2.p2Command.imports}

/-- A host satisfying a theory satisfies its consequences. -/
theorem hostSat_mono {P Q : List WEv → Prop} (h : ∀ t, P t → Q t) {I : Set FnName}
    {η : Host Y I} (hη : (hostSat P).holds η) : (hostSat Q).holds η :=
  fun s hs => h _ (hη s hs)

/-- **Typing over every 0.2 host.** -/
theorem p3OverP2_typed {ST : Type} {T : Protocol ST WEv} (hη : (hostSat T.Accepts).holds η) :
    (hostSat typed3.Accepts).holds (link η p3OverP2) :=
  link_model (typed_sat T) hη

/-- **The saturated clock over every 0.2 host.** -/
theorem p3OverP2_clock {ST : Type} {T : Protocol ST WEv} (hη : (hostSat T.Accepts).holds η) :
    (hostSat clockTh3s.Accepts).holds (link η p3OverP2) :=
  link_model (clock_sat T) hη

/-- **Loose stdout over every 0.2 host.** -/
theorem p3OverP2_stdout {ST : Type} {T : Protocol ST WEv} (hη : (hostSat T.Accepts).holds η) :
    (hostSat stdoutTh3w.Accepts).holds (link η p3OverP2) :=
  link_model (stdout_sat T) hη

/-- **Loose reads over every 0.2 host of the read theory over the same contents.** -/
theorem p3OverP2_read (F : BitVec 32 → List (BitVec 8))
    (hη : (hostSat (fsRead2 F).Accepts).holds η) :
    (hostSat (fsReadTh3w F).Accepts).holds (link η p3OverP2) :=
  link_model (read_sat F) hη

/-- **WASI 0.3 over 0.2 is an implementation morphism**: over every host of the loose 0.2
theory with the file contents `F`, the composite is a model of the 0.3 theory `p3Th F`. -/
theorem p3OverP2_model (F : BitVec 32 → List (BitVec 8))
    (hη : (hostSat (p2ThF F).Accepts).holds η) :
    (hostSat (p3Th F).Accepts).holds (link η p3OverP2) := by
  have h2 : (hostSat (fsRead2 F).Accepts).holds η :=
    hostSat_mono (fun t ht => ((Protocol.accepts_prod_iff _ _ t).1 ht).2) hη
  intro s hs
  simp only [p3Th, Protocol.accepts_prod_iff]
  exact ⟨p3OverP2_typed hη s hs, p3OverP2_clock hη s hs, p3OverP2_stdout hη s hs,
    p3OverP2_read F h2 s hs⟩

/-- **Over the loose host of the 0.2 theory**, the composite is a 0.3 model. -/
theorem p3OverP2_loose (F : BitVec 32 → List (BitVec 8)) :
    (hostSat (p3Th F).Accepts).holds
      (link (loose (Y := Y) (I := P2.p2Command.imports) (p2ThF F)) p3OverP2) :=
  p3OverP2_model F (loose_sat _)

end Silmaril.Wasi.Versions.P3OverP2
