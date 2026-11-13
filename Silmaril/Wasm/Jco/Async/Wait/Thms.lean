module

public import Silmaril.Wasm.Jco.Async.Wait.Defs
public import Silmaril.Wasm.Jco.Async.Native.Thms
public import Silmaril.Proofs.Wasm.Jco.Async.Wait

/-!
# Natively async bodies that wait or use streams: results

Proofs in `Silmaril.Proofs.Wasm.Jco.Async.Wait`.

**The general form.** A natively async body that runs `M`'s export, lifts its results to the
values `ws` and then runs an epilogue `E` (any built-ins, any callback code) has, under
`canon lift async`, exactly the caller-visible behaviour of `M`'s C convention, as long as the
epilogue's tail returns `ws` faithfully (`EpiOk`):

* **`asyncCall_fstIs`**: such a call is `visible m₀` (the C convention `m₀` over `M`, its values
  read back at the result type) over `M`'s state: the same values, the same states of `M`, the
  same traps. Only the async store may differ.
* `retE_epiOk`, `yieldE_epiOk`, `inlines_epilogues`: the adaptor's epilogue (exit at once, both
  styles) and the yielding one return the values faithfully from every store. So every module
  of `NInst.Inlines` (the condition of `recognizeThinA_agrees`) has faithful epilogues.
* **`recognizeThinA_sameFst`**: a recognized thin async wrapper of a module with faithful
  epilogues agrees with `awrap md` up to the async store (`SameFst`), from every store where
  the epilogues are faithful. For `NInst.Inlines` modules `recognizeThinA_agrees` gives the
  equation; here the store may differ, so the statement is about `M`'s side.

**Streams and waits.**

* `drive_wait_iff`: with a callback answering `EXIT`, the runtime's loop on `WAIT si` takes
  the event of some member of `si` (any ready one, `Waits`) and ends; it has no other outcome.
* **`pipeE_epiOk`**: passing the values through a stream (`stream.new`, a pending
  `stream.write`, the rendezvous `stream.read`, `task.return` of the items read) is faithful on
  a fresh channel.
* **`pipeWaitE_epiOk`**: the same followed by `WAIT` on a new set joined by the writable end
  (which holds the rendezvous's `stream-write` event) is faithful on `Fresh` stores.
* **`recognizeThinA_piped`**, **`recognizeThinA_pipedWait`**: the thin async wrappers of the
  modules `NInst.piped M md` and `NInst.pipedWait M md` (names distinct; for the waiting one,
  every async function in the callback style) agree with `awrap md` up to the async store.
* **`asyncCall_waitE_noOk`**: a body that returns its values and then waits on a fresh empty set
  never returns to its caller: the runtime's loop of this model runs to the end before the
  caller reads the results, and the set never gets an event.

Not covered: a body that waits for an event that only another party (the caller, a host) can
cause. Here the callback loop runs before the caller sees the results, so such a body does not
return (`asyncCall_waitE_noOk` is the simplest case); the Component Model lets the caller
continue at `task.return`. Also not covered: callbacks that do work (here they only answer
`EXIT`), cancellation and backpressure.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Async

open Silmaril.Wasm.Component (Flat Val)
open Silmaril.Wasm.Component.Async (Store Waits)
open Silmaril.Proofs.Wasm.Jco.Async.Wait

variable (M : CoreInst)

/-- **An async call whose epilogue returns the values faithfully is `visible m₀` over `M`'s
state.** -/
theorem asyncCall_fstIs (R core cb : List Flat → RM M.withStore.St (List Flat))
    (E : Nat → List Val → RM M.withStore.St (List Flat)) (sty : Style) (sig : Sig)
    (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) (s : M.withStore.St)
    (hE : EpiOk M E cb sty s.2) :
    FstIs M (asyncCall M R (bodyWith M core sig.result E) cb sty sig vs)
      (visible M m₀ sig.result) s :=
  fstIs_of_epiOk M R core cb E sty sig vs m₀ hc s hE

/-- The adaptor's epilogue returns the values faithfully from every store. -/
theorem retE_epiOk (cb : List Flat → RM M.withStore.St (List Flat)) (sty : Style) (st : Store) :
    EpiOk M (retE M sty) cb sty st :=
  Silmaril.Proofs.Wasm.Jco.Async.Wait.retE_epiOk M cb sty st

/-- The yielding epilogue, with a callback answering `EXIT`, returns the values faithfully. -/
theorem yieldE_epiOk (cb : List Flat → RM M.withStore.St (List Flat))
    (hcb : ∀ a, cb a = pure [i32n cbExit]) (st : Store) : EpiOk M (yieldE M) cb .callback st :=
  Silmaril.Proofs.Wasm.Jco.Async.Wait.yieldE_epiOk M cb hcb st

/-- Modules that inline the adaptor's epilogue have faithful epilogues. -/
theorem inlines_epilogues (N : NInst M) (md : AMeta) (hN : N.Inlines md) :
    N.Epilogues md fun _ => True :=
  Silmaril.Proofs.Wasm.Jco.Async.Wait.inlines_epilogues M N md hN

/-- **`WAIT` with a callback answering `EXIT`**: one event of a member is taken, then the loop
ends. -/
theorem drive_wait_iff (si : Nat) (hsi : 16 * si + 2 < 2 ^ 32) (s : M.withStore.St)
    (o : Out M.withStore.St Unit) :
    Drive M (exitCb M) (waitCode si) s o ↔
      ∃ h e st', Waits s.2 si h e st' ∧ o = .ok () (s.1, st') :=
  Silmaril.Proofs.Wasm.Jco.Async.Wait.drive_wait_iff M si hsi s o

/-- **The values through a stream** are returned faithfully on a fresh channel. -/
theorem pipeE_epiOk (cb : List Flat → RM M.withStore.St (List Flat)) (sty : Style) (st : Store)
    (hf : st.chans (st.next + 1) = {}) : EpiOk M (pipeE M sty.exitResult) cb sty st :=
  Silmaril.Proofs.Wasm.Jco.Async.Wait.pipeE_epiOk M cb sty st hf

/-- **Through a stream, then `WAIT`**: returned faithfully on `Fresh` stores. -/
theorem pipeWaitE_epiOk (st : Store) (hF : Fresh st) :
    EpiOk M (pipeWaitE M) (exitCb M) .callback st :=
  Silmaril.Proofs.Wasm.Jco.Async.Wait.pipeWaitE_epiOk M st hF

/-- **A body that waits on an empty set never returns a value to its caller.** -/
theorem asyncCall_waitE_noOk (R core : List Flat → RM M.withStore.St (List Flat)) (sig : Sig)
    (vs : List PVal) (m₀ : RM M.St (Option PVal))
    (hc : canonCall M.withStore R core sig vs = RM.liftFst m₀) (s : M.withStore.St)
    (hj : ∀ h, s.2.joined h ≠ some (s.2.next + 1)) (hsi : 16 * (s.2.next + 1) + 2 < 2 ^ 32)
    (r : Option PVal) (s' : M.withStore.St) :
    ¬ asyncCall M R (bodyWith M core sig.result (waitE M)) (exitCb M) .callback sig vs s
      (.ok r s') :=
  Silmaril.Proofs.Wasm.Jco.Async.Wait.asyncCall_waitE_noOk M R core sig vs m₀ hc s hj hsi r s'

/-- **A recognized thin async wrapper of a module with faithful epilogues agrees with
`awrap md` up to the async store.** -/
theorem recognizeThinA_sameFst (N : NInst M) {md : AMeta} {r : String} {c : NComp}
    {P : Store → Prop} (h : recognizeThinA md r = some c) (hC : md.sync.Conforms M)
    (hR : ReallocAgrees M md.sync r) (hN : N.Epilogues md P) (name : String) (vs : List PVal)
    (s : M.withStore.St) (hP : P s.2) :
    SameFst M (c.callExport N name vs) ((awrap md).callExport M name vs) s := by
  obtain ⟨hk, rfl⟩ := recognizeThinA_eq h
  have hp : ∀ s ∈ md.world, ∀ vs, lowerParams M.withStore (M.withStore.call r) s.sig.params vs =
      md.sync.specParams M.withStore s.sig.params vs := fun s _ vs =>
    lowerParams_realloc M.withStore md.sync
      (Silmaril.Proofs.Wasm.Jco.Async.Native.reallocAgrees_withStore M md.sync r hR) s.sig.params vs
  rw [thinA_callExport, awrap_correct M md hC]
  exact canonSpecA_sameFst M N md r hN hk hp name vs s hP

/-- **The module whose bodies pass the values through a stream** agrees with `awrap md` up to the
async store, from every store with a fresh channel at the stream's handle. -/
theorem recognizeThinA_piped {md : AMeta} {r : String} {c : NComp}
    (h : recognizeThinA md r = some c) (hn : (md.world.map (·.sig.name)).Nodup)
    (hC : md.sync.Conforms M) (hR : ReallocAgrees M md.sync r) (name : String) (vs : List PVal)
    (s : M.withStore.St) (hf : s.2.chans (s.2.next + 1) = {}) :
    SameFst M (c.callExport (NInst.piped M md) name vs) ((awrap md).callExport M name vs) s :=
  recognizeThinA_sameFst M _ h hC hR (piped_epilogues M md hn) name vs s hf

/-- **The module whose bodies pass the values through a stream and then wait** agrees with
`awrap md` up to the async store, from every `Fresh` store, when every async function is in the
callback style. -/
theorem recognizeThinA_pipedWait {md : AMeta} {r : String} {c : NComp}
    (h : recognizeThinA md r = some c) (hn : (md.world.map (·.sig.name)).Nodup)
    (hcb : ∀ s ∈ md.world, ∀ sty, s.async = some sty → sty = .callback)
    (hC : md.sync.Conforms M) (hR : ReallocAgrees M md.sync r) (name : String) (vs : List PVal)
    (s : M.withStore.St) (hF : Fresh s.2) :
    SameFst M (c.callExport (NInst.pipedWait M md) name vs) ((awrap md).callExport M name vs) s :=
  recognizeThinA_sameFst M _ h hC hR (pipedWait_epilogues M md hn hcb) name vs s hF

end Silmaril.Wasm.Jco.Async

/--
info: 'Silmaril.Wasm.Jco.Async.recognizeThinA_pipedWait' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Jco.Async.recognizeThinA_pipedWait

/--
info: 'Silmaril.Wasm.Jco.Async.asyncCall_waitE_noOk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Jco.Async.asyncCall_waitE_noOk
