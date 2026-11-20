module

public import Silmaril.Wasm.Component.Reference.HostWrite.Defs
public import Silmaril.Wasm.Component.Reference.Laws.Thms

/-!
# Host-safe programs: the program logic

* `HostSafe.mono`: a program with no pending read is host-safe with any pending read;
* `HostSafe.bind`: host-safety is closed under sequencing with host-safe continuations;
* `HostSafe.of_every`: a program none of whose operations writes the host state
  (`Prog.Every (Op.PreservesInvW I (fun _ => False))`, in particular
  `P.InvW I (fun _ => False)`) is host-safe for every `Ext`;
* `HostSafe.confine`: confining a host-safe program keeps it host-safe;
* the inversions `HostSafe.of_op`, `HostSafe.of_get`, `HostSafe.of_set`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime

variable {E : CoreEngine} {σ : Type} {α β : Type} {Ext : σ → σ → Prop}

namespace HostSafe

/-- A program with no pending read is host-safe with any pending read. -/
theorem mono {p : P E σ α} (h : HostSafe Ext none p) (c : Option σ) : HostSafe Ext c p := by
  cases h with
  | pure _ a => exact .pure c a
  | op _ ho hk => exact .op c ho hk
  | get _ hk => exact .get c hk

/-- **Sequencing.** -/
theorem bind {c : Option σ} {p : P E σ α} {f : α → P E σ β} (h : HostSafe Ext c p)
    (hf : ∀ a, HostSafe Ext none (f a)) : HostSafe Ext c (p >>= f) := by
  induction h with
  | pure c a => exact (hf a).mono c
  | op c ho _ ih => exact .op c ho ih
  | get c _ ih => exact .get c ih
  | set he _ ih => exact .set he ih

/-- **Programs that never write the host state are host-safe.** -/
theorem of_every {I : CStore E → Prop} {p : P E σ α}
    (h : Prog.Every (S := Eff E σ) (Op.PreservesInvW I (fun _ : σ => False)) p) (c : Option σ) :
    HostSafe Ext c p := by
  induction h generalizing c with
  | pure a => exact .pure c a
  | @op o k hQ _ ih =>
    cases o with
    | hostGet => exact .get c fun s => ih s (some s)
    | hostSet s => exact hQ.elim
    | get => exact .op c trivial fun r => ih r none
    | modify f => exact .op c trivial fun r => ih r none
    | trap r => exact .op c trivial fun r => ih r none
    | choose k => exact .op c trivial fun r => ih r none
    | callCore f args => exact .op c trivial fun r => ih r none
    | call cl => exact .op c trivial fun r => ih r none
    | currentThread => exact .op c trivial fun r => ih r none
    | newThread b => exact .op c trivial fun r => ih r none
    | block t => exact .op c trivial fun r => ih r none
    | resumeThread t => exact .op c trivial fun r => ih r none
    | emit o => exact .op c trivial fun r => ih r none
    | readCore => exact .op c trivial fun r => ih r none
    | memWrite m ptr bytes => exact .op c trivial fun r => ih r none
    | allocHost ty h => exact .op c trivial fun r => ih r none
    | prepare md imports => exact .op c trivial fun r => ih r none

/-- `P.InvW I (fun _ => False)` programs are host-safe. -/
theorem of_invW {I : CStore E → Prop} {p : P E σ α} (h : P.InvW I (fun _ : σ => False) p)
    (c : Option σ) : HostSafe Ext c p := of_every h c

/-- **Confining a host-safe program keeps it host-safe.** -/
theorem confine {c : Option σ} {p : P E σ α} (h : HostSafe Ext c p) :
    HostSafe Ext c (Canon.confine p) := by
  induction h with
  | pure c a => exact .pure c a
  | @op c o k ho _ ih =>
    show HostSafe Ext c (if Op.observes o then _ else _)
    split
    · exact .op c ho ih
    · exact .op c trivial fun e => nomatch e
  | get c _ ih => exact .get c ih
  | set he _ ih => exact .set he ih

/-! ## Inversions -/

/-- The continuations of a plain operation have no pending read. -/
theorem of_op {c : Option σ} {o : Op E σ} {k : (Eff E σ).Resp o → P E σ α} (ho : o.Plain)
    (h : HostSafe Ext c (.op (S := Eff E σ) o k)) : ∀ r, HostSafe Ext none (k r) := by
  cases h with
  | op _ _ hk => exact hk
  | get _ _ => exact ho.elim
  | set _ _ => exact ho.elim

/-- The continuation of a read has the read pending. -/
theorem of_get {c : Option σ} {k : σ → P E σ α}
    (h : HostSafe Ext c (.op (S := Eff E σ) .hostGet k)) : ∀ s, HostSafe Ext (some s) (k s) := by
  cases h with
  | op _ ho _ => exact ho.elim
  | get _ hk => exact hk

/-- **A write follows a read and is allowed by `Ext`.** -/
theorem of_set {c : Option σ} {s' : σ} {k : Unit → P E σ α}
    (h : HostSafe Ext c (.op (S := Eff E σ) (.hostSet s') k)) :
    ∃ s, c = some s ∧ Ext s s' ∧ HostSafe Ext none (k ()) := by
  cases h with
  | op _ ho _ => exact ho.elim
  | set he hk => exact ⟨_, rfl, he, hk⟩

end HostSafe

end Silmaril.Wasm.Component.Canon
