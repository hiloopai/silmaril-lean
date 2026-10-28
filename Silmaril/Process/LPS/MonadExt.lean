module

public import Silmaril.Process.LPS.Monad
public import Silmaril.Process.LPS.StateHelpers

/-!
# LPS in Lean: the rest of the specification monad

Translation of the readers, accessors and setters of LPS `Monad.v:285-360` (upstream commit
`f1006fe8`) that `Monad.lean` does not cover, and of the introduction lemmas of
`Monad.v:362-424`. The `Model` accessors and setters of `State.v:3440-3881` they need are the
ones of `StateHelpers`.

Each setter is `modify` of the matching `State.v` `with_*` function, as in LPS. The `Model`
setters below rebuild exactly the field LPS's `mkModelOf … (mkProcState …)` rebuilds and carry
every other field across.
-/

@[expose] public section

namespace Silmaril.Process.LPS

namespace Sys

/-- LPS `Monad.v:286` `sysno`. -/
def sysno : Sys Word := fun i m o => o = .ok i.sysno m []
/-- LPS `Monad.v:287` `arg`. -/
def arg (k : Nat) : Sys Word := fun i m o => o = .ok (i.arg k) m []

/-- LPS `Monad.v:313` `get_fds`. -/
def getFds : Sys (List (Word × FdEntry)) := fun _ m o => o = .ok m.fds m []

/-- LPS `Monad.v:316` `set_fds`. -/
def setFds (fds : List (Word × FdEntry)) : Sys Unit := modify (·.withFds fds)
/-- LPS `Monad.v:317` `set_pipes`. -/
def setPipes (ps : List (Word × PipeBuf)) : Sys Unit := modify (·.withPipes ps)
/-- LPS `Monad.v:318` `set_vmmaps`. -/
def setVmmaps (h : VmMaps) : Sys Unit := modify (·.withVmmaps h)
/-- LPS `Monad.v:319` `add_vm_lazy`. -/
def addVmLazy (a n : Word) : Sys Unit := modify (vmAddLazy a n)
/-- LPS `Monad.v:320` `forget_vm_range`. -/
def forgetVmRange (lo hi : Int) : Sys Unit := modify (vmForgetRange lo hi)
/-- LPS `Monad.v:322` `set_stdin`. -/
def setStdin (s : InputStream) : Sys Unit := modify (·.withStdin s)
/-- LPS `Monad.v:323` `set_urandom`. -/
def setUrandom (s : InputStream) : Sys Unit := modify (·.withUrandom s)
/-- LPS `Monad.v:324` `set_fs`. -/
def setFs (fs : Fs.FileSystem) : Sys Unit := modify (·.withFs fs)
/-- LPS `Monad.v:325` `set_halted`. -/
def setHalted (code : Word) : Sys Unit := modify (·.withHalted code)
/-- LPS `Monad.v:326` `set_tid`. -/
def setTid (tid : Word) : Sys Unit := modify (·.withTid tid)
/-- LPS `Monad.v:327` `set_creds`. -/
def setCreds (c : Creds) : Sys Unit := modify (·.withCreds c)
/-- LPS `Monad.v:329` `set_rlimit_core`. -/
def setRlimitCore (bs : List Byte) : Sys Unit := modify (·.withRlimitCore bs)
/-- LPS `Monad.v:336` `set_utsname`. -/
def setUtsname (bs : List Byte) : Sys Unit := modify (·.withUtsname bs)
/-- LPS `Monad.v:338` `set_setsid_succeeded`. -/
def setSetsidSucceeded : Sys Unit := modify (·.withSetsidSucceeded)
/-- LPS `Monad.v:343` `set_statpin`. -/
def setStatpin (p : Fs.Path) (bs : List Byte) : Sys Unit := modify (·.withStatpin p bs)
/-- LPS `Monad.v:347` `set_sigmask`. -/
def setSigmask (sm : Word) : Sys Unit := modify (·.withSigmask sm)
/-- LPS `Monad.v:349` `set_sigaltstack_installed`. -/
def setSigaltstackInstalled : Sys Unit := modify (·.withSigaltstackInstalled)
/-- LPS `Monad.v:356` `set_sigabrt_pending`. -/
def setSigabrtPending : Sys Unit := modify (·.withSigabrtPending)
/-- LPS `Monad.v:357` `set_killed`. -/
def setKilled (sig : Word) : Sys Unit := modify (·.withKilled sig)
/-- LPS `Monad.v:360` `set_clock`. -/
def setClock (t : Word) : Sys Unit := modify (·.withClock t)

/-! ## Introduction lemmas (LPS `Monad.v:362-424`) -/

section Intro

variable {α β : Type}

/-- LPS `Monad.v:299` `bind_get_model`: reading the model is pure. -/
theorem bind_getModel (k : Model → Sys α) (i : SyscallInput) (m : Model) (o : Outcome α) :
    bind getModel k i m o ↔ k m i m o := by
  cases o with
  | ok y m₂ evs =>
    constructor
    · rintro ⟨x, m₁, evs₁, evs₂, h₁, h₂, rfl⟩
      cases h₁
      simpa using h₂
    · intro h
      exact ⟨m, m, [], evs, rfl, h, by simp⟩
  | unmodeled =>
    constructor
    · rintro (h | ⟨x, m₁, evs₁, h₁, h₂⟩)
      · cases h
      · cases h₁
        exact h₂
    · intro h
      exact .inr ⟨m, m, [], rfl, h⟩

/-- LPS `Monad.v:368` `bind_ok`. -/
theorem bind_ok (c : Sys α) (k : α → Sys β) (i : SyscallInput) (m : Model) (x : α) (m₁ : Model)
    (evs₁ : List Event) (y : β) (m₂ : Model) (evs₂ : List Event) (hc : c i m (.ok x m₁ evs₁))
    (hk : k x i m₁ (.ok y m₂ evs₂)) : bind c k i m (.ok y m₂ (evs₁ ++ evs₂)) :=
  ⟨x, m₁, evs₁, evs₂, hc, hk, rfl⟩

/-- LPS `Monad.v:374` `bind_unmodeled1`. -/
theorem bind_unmodeled₁ (c : Sys α) (k : α → Sys β) (i : SyscallInput) (m : Model)
    (hc : c i m .unmodeled) : bind c k i m .unmodeled := .inl hc

/-- LPS `Monad.v:378` `bind_unmodeled2`. -/
theorem bind_unmodeled₂ (c : Sys α) (k : α → Sys β) (i : SyscallInput) (m : Model) (x : α)
    (m₁ : Model) (evs₁ : List Event) (hc : c i m (.ok x m₁ evs₁)) (hk : k x i m₁ .unmodeled) :
    bind c k i m .unmodeled := .inr ⟨x, m₁, evs₁, hc, hk⟩

/-- LPS `Monad.v:382` `pure_ok`. -/
theorem pure_ok (x : α) (i : SyscallInput) (m : Model) : pure x i m (.ok x m []) := rfl
/-- LPS `Monad.v:385` `choose_ok`. -/
theorem choose_ok (P : α → Prop) (x : α) (i : SyscallInput) (m : Model) (h : P x) :
    choose P i m (.ok x m []) := ⟨x, h, rfl⟩
/-- LPS `Monad.v:388` `unmodeled_intro`. -/
theorem unmodeled_intro (i : SyscallInput) (m : Model) : (unmodeled : Sys α) i m .unmodeled := rfl
/-- LPS `Monad.v:391` `alt_l`. -/
theorem alt_l (c₁ c₂ : Sys α) (i : SyscallInput) (m : Model) (o : Outcome α) (h : c₁ i m o) :
    alt c₁ c₂ i m o := .inl h
/-- LPS `Monad.v:394` `alt_r`. -/
theorem alt_r (c₁ c₂ : Sys α) (i : SyscallInput) (m : Model) (o : Outcome α) (h : c₂ i m o) :
    alt c₁ c₂ i m o := .inr h
/-- LPS `Monad.v:397` `emit_ok`. -/
theorem emit_ok (evs : List Event) (i : SyscallInput) (m : Model) : emit evs i m (.ok () m evs) :=
  rfl
/-- LPS `Monad.v:400` `input_ok`. -/
theorem input_ok (i : SyscallInput) (m : Model) : input i m (.ok i m []) := rfl
/-- LPS `Monad.v:403` `sysno_ok`. -/
theorem sysno_ok (i : SyscallInput) (m : Model) : sysno i m (.ok i.sysno m []) := rfl
/-- LPS `Monad.v:406` `arg_ok`. -/
theorem arg_ok (k : Nat) (i : SyscallInput) (m : Model) : arg k i m (.ok (i.arg k) m []) := rfl
/-- LPS `Monad.v:409` `get_model_ok`. -/
theorem getModel_ok (i : SyscallInput) (m : Model) : getModel i m (.ok m m []) := rfl
/-- LPS `Monad.v:412` `get_fds_ok`. -/
theorem getFds_ok (i : SyscallInput) (m : Model) : getFds i m (.ok m.fds m []) := rfl
/-- LPS `Monad.v:415` `get_vmmaps_ok`. -/
theorem getVmmaps_ok (i : SyscallInput) (m : Model) : getVmmaps i m (.ok m.vmmaps m []) := rfl
/-- LPS `Monad.v:418` `modify_ok`. -/
theorem modify_ok (f : Model → Model) (i : SyscallInput) (m : Model) :
    modify f i m (.ok () (f m) []) := rfl

end Intro

end Sys

end Silmaril.Process.LPS
