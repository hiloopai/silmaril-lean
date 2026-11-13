module

public import Silmaril.Wasm.Jco.Async.Stackful.Defs
public import Silmaril.Wasm.Jco.Async.Early.Thms

/-!
# The stackful style after `task.return`: proofs

Proofs of `Silmaril.Wasm.Jco.Async.Stackful.Thms`.

* `atomic_post_iff`: a run of the atomic rest is `run`, then `Drive`.
* `atomic_srest`: an atomic run is a run of `SRest` with no other party.
* `streamThread_atomic_hangs`: the atomic rest of the stackful stream function has no outcome.
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Async.Stackful

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Jco.Async
open Silmaril.Wasm.Component (Flat Val)
open Silmaril.Wasm.Component.Async (Store)
open Silmaril.Proofs.Wasm.Jco.Async.Early (sB sD)

variable (M : CoreInst)

/-- The outcomes of the atomic rest. -/
theorem atomic_post_iff {L : Type} (th : SThread M L) (t : Nat) (l : L) (s : M.withStore.St)
    (o : Out M.withStore.St (List Flat)) :
    th.atomic.post t l s o ↔
      (∃ rs s₁, th.run t l s (.ok rs s₁) ∧
        ((∃ s', Drive M (th.resume t l) rs s₁ (.ok () s') ∧ o = .ok [] s') ∨
          (Drive M (th.resume t l) rs s₁ .trap ∧ o = .trap))) ∨
      (th.run t l s .trap ∧ o = .trap) := by
  show RM.bind _ _ s o ↔ _
  simp only [RM.bind]
  constructor
  · rintro (⟨rs, s₁, hr, (⟨u, s', hd, hp⟩ | ⟨hd, ho⟩)⟩ | h)
    · exact .inl ⟨rs, s₁, hr, .inl ⟨s', hd, hp⟩⟩
    · exact .inl ⟨rs, s₁, hr, .inr ⟨hd, ho⟩⟩
    · exact .inr h
  · rintro (⟨rs, s₁, hr, (⟨s', hd, hp⟩ | ⟨hd, ho⟩)⟩ | h)
    · exact .inl ⟨rs, s₁, hr, .inl ⟨(), s', hd, hp⟩⟩
    · exact .inl ⟨rs, s₁, hr, .inr ⟨hd, ho⟩⟩
    · exact .inr h

/-- **An atomic run of the thread is a run of `SRest`** (with no other party). -/
theorem atomic_srest {L : Type} (th : SThread M L) (t : Nat) (l : L) (s s' : M.withStore.St)
    (rs' : List Flat) (h : th.atomic.post t l s (.ok rs' s')) : SRest M th t l s s' := by
  rcases (atomic_post_iff M th t l s _).1 h with ⟨rs, s₁, hr, (⟨s₂, hd, ho⟩ | ⟨-, ho⟩)⟩ | ⟨-, ho⟩
  · cases ho
    exact ⟨rs, s₁, hr, drive_finish M _ rs s₁ _ hd⟩
  · cases ho
  · cases ho

/-- **The atomic rest of the stackful stream function has no outcome**: its wait finds no
pending event, and no reader can run. -/
theorem streamThread_atomic_hangs (st : Store) (hU : Unused st)
    (hb : 16 * (st.next + 3) + 2 < 2 ^ 32) (ws : List Val) (x : M.St)
    (o : Out M.withStore.St (List Flat)) :
    ¬ (streamThread M).atomic.post st.next (st.next + 2, ws) (x, sB st) o := by
  intro h
  have hrun := stream_post M st hU ws x
  rcases (atomic_post_iff M _ _ _ _ o).1 h with ⟨rs, s₁, hr, hd⟩ | ⟨hr, -⟩
  · have hr' : Out.ok rs s₁ = Out.ok (waitCode (st.next + 3)) (x, sD st ws) :=
      (congrFun hrun _).mp hr
    cases hr'
    rcases hd with ⟨s', hd, -⟩ | ⟨hd, -⟩
    · exact stream_hangs M st hU hb ws x _ _ hd
    · exact stream_hangs M st hU hb ws x _ _ hd
  · have hr' : (Out.trap : Out M.withStore.St (List Flat)) =
        Out.ok (waitCode (st.next + 3)) (x, sD st ws) := (congrFun hrun _).mp hr
    cases hr'

end Silmaril.Proofs.Wasm.Jco.Async.Stackful
