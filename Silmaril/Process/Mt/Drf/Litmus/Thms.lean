module

public import Silmaril.Process.Mt.Drf.Litmus.Defs
public import Silmaril.Process.Mt.Drf.Thms
import Silmaril.Proofs.Process.Mt.Drf.Litmus

/-!
# Litmus tests: the bridge's hypothesis is needed, and sufficient on synchronised versions

Everything here is proved (standard axioms only); proofs are in
`Silmaril/Proofs/Process/Mt/Drf/Litmus.lean`.

* **Racy versions break.** `sb_tso`: racy `SB` reaches "both loads read `0`" on the TSO
  machine (drained). `mp_xl`: racy `MP` (non-temporal data store, plain flag store) reaches
  "flag seen, data not seen" on the XL machine. Neither outcome is SC (`sb_sc`, `mp_sc`), so
  neither program has an ownership certificate (`sbRacy_not_cert`, `mpRacy_not_cert`).
* **Locked versions are fine.** With `xchg` for the stores (`SB`) or for the flag store
  (`MP`), the programs are race free modulo synchronisation (`sbLocked_cert`,
  `mpLocked_cert`; in `MP` the data cell's ownership moves from the writer to the reader
  through the flag), and the bridge rules the weak outcomes out under TSO and XL
  (`sbLocked_buffered`, `mpLocked_buffered`).
-/

@[expose] public section

namespace Silmaril.Process.Mt.Drf.Litmus

open Silmaril.Process.Mt.Drf

/-- `SB` (racy or locked) has no weak outcome on the SC machine. -/
theorem sb_sc {lk : Bool} {C : Cfg (sys (sb lk))} (h : ScReach (sys (sb lk)) 2 (init _) C) :
    ¬ sbWeak C.ts := Silmaril.Proofs.Process.Mt.Drf.Litmus.sb_sc h

/-- `MP` (racy or locked) has no weak outcome on the SC machine. -/
theorem mp_sc {lk : Bool} {C : Cfg (sys (mp lk))} (h : ScReach (sys (mp lk)) 2 (init _) C) :
    ¬ mpWeak C.ts := Silmaril.Proofs.Process.Mt.Drf.Litmus.mp_sc h

/-- **Racy `SB` breaks under TSO**: the TSO machine reaches its weak outcome, drained. -/
theorem sb_tso : ∃ C : BCfg (sys (sb false)),
    BReach .tso (sys (sb false)) 2 (init _).toB C ∧ C.Drained ∧ sbWeak C.ts :=
  Silmaril.Proofs.Process.Mt.Drf.Litmus.sb_tso

/-- **Racy `MP` breaks under XL**: the flag store overtakes the non-temporal data store. -/
theorem mp_xl : ∃ C : BCfg (sys (mp false)),
    BReach .xl (sys (mp false)) 2 (init _).toB C ∧ mpWeak C.ts :=
  Silmaril.Proofs.Process.Mt.Drf.Litmus.mp_xl

/-- Racy `SB` has no ownership certificate. -/
theorem sbRacy_not_cert :
    ¬ ∃ (R : Cfg (sys (sb false)) → Own → Prop) (o : Own), Cert (sys (sb false)) 2 R ∧
      R (init _) o := Silmaril.Proofs.Process.Mt.Drf.Litmus.sbRacy_not_cert

/-- Racy `MP` has no ownership certificate. -/
theorem mpRacy_not_cert :
    ¬ ∃ (R : Cfg (sys (mp false)) → Own → Prop) (o : Own), Cert (sys (mp false)) 2 R ∧
      R (init _) o := Silmaril.Proofs.Process.Mt.Drf.Litmus.mpRacy_not_cert

/-- Locked `SB` has a certificate (nobody owns anything). -/
theorem sbLocked_cert : Cert (sys (sb true)) 2 (fun _ o => ∀ t a, ¬ o t a) :=
  Silmaril.Proofs.Process.Mt.Drf.Litmus.sbLocked_cert

/-- Locked `MP` has a certificate (the data cell moves through the flag). -/
theorem mpLocked_cert : Cert (sys (mp true)) 2 MpR :=
  Silmaril.Proofs.Process.Mt.Drf.Litmus.mpLocked_cert

/-- **Locked `SB` has no weak outcome under TSO or XL.** -/
theorem sbLocked_buffered {M : Model} {C : BCfg (sys (sb true))}
    (h : BReach M (sys (sb true)) 2 (init _).toB C) : ¬ sbWeak C.ts :=
  Silmaril.Proofs.Process.Mt.Drf.Litmus.sbLocked_buffered h

/-- **Locked `MP` has no weak outcome under TSO or XL.** -/
theorem mpLocked_buffered {M : Model} {C : BCfg (sys (mp true))}
    (h : BReach M (sys (mp true)) 2 (init _).toB C) : ¬ mpWeak C.ts :=
  Silmaril.Proofs.Process.Mt.Drf.Litmus.mpLocked_buffered h

end Silmaril.Process.Mt.Drf.Litmus
