module

public import Silmaril.Machine.Process.IoSpecNet.Defs
public import Silmaril.Machine.Process.IoSpec.Thms

/-!
# `IoSpecNet`: theorems

PROVED (standard axioms):

* **The embedding**: `lpsPart_liftT` (the LPS part of an embedded trace is the trace),
  `sockPart_liftT` (it has no socket event), `lpsPart_append`, `sockPart_append`,
  `liftT_injective`, `netOk_liftT` (an embedded trace is admitted by every network),
  `netOk_append`.
* **`xioSafe_lift_iff`**: for every LPS environment `E`, frame exits `Q` and trace predicate
  `A`, `XIoSafeN step (SysEnv.lift E) (liftQ Q) n m e (liftA A) ↔ IoSafeN step E Q n m e A`.
  Existing `IoSafeN` results (the hello, write and read arms of `IoSpec`) hold unchanged for the
  embedded environment.
* **`xioSafe_psafe`**: LPS soundness (`IoSpec.ioSafe_psafe`) transported along the embedding:
  extended safety of a lifted sound environment gives `PSafeF` for the LPS predicate `A`.
* **`withNet_arm_netOk`**: every answer of `withNet E N H` emits a trace `NetOk N` admits (the
  embedded LPS events trivially, the socket events by `sockArm`); `withNet_lift_arm`: the
  answers of `E` are answers of `withNet E N H`.

What is **not** proved: soundness of `sockArm` for any OS model (LPS has no socket syscalls).
-/

@[expose] public section

namespace Silmaril.Machine.Process.IoSpecNet

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec

variable {V : Type}

/-! ## The embedding -/

/-- The LPS part of an embedded trace is the trace. -/
theorem lpsPart_liftT (t : List Event) : lpsPart (liftT (V := V) t) = t := by
  induction t with
  | nil => rfl
  | cons e t ih => simpa [lpsPart, liftT, XEvent.toLps] using ih

/-- An embedded trace has no socket event. -/
theorem sockPart_liftT (t : List Event) : sockPart (liftT (V := V) t) = [] := by
  induction t with
  | nil => rfl
  | cons e t ih => simp [sockPart, liftT, XEvent.toSock]

/-- The LPS part of a concatenation. -/
theorem lpsPart_append (t u : List (XEvent V)) : lpsPart (t ++ u) = lpsPart t ++ lpsPart u := by
  simp [lpsPart]

/-- The socket part of a concatenation. -/
theorem sockPart_append (t u : List (XEvent V)) :
    sockPart (t ++ u) = sockPart t ++ sockPart u := by
  simp [sockPart]

/-- The embedding is injective. -/
theorem liftT_injective : Function.Injective (liftT (V := V)) := fun t u h => by
  rw [← lpsPart_liftT (V := V) t, h, lpsPart_liftT]

/-- The socket part of socket events. -/
theorem sockPart_map_sock (evs : List (SockEv V)) : sockPart (evs.map XEvent.sock) = evs := by
  induction evs with
  | nil => rfl
  | cons e t ih => simpa [sockPart, XEvent.toSock] using ih

/-- Every network admits an embedded trace. -/
theorem netOk_liftT (N : NetEnv V) (t : List Event) : NetOk N (liftT t) := fun e he => by
  rw [sockPart_liftT] at he
  exact absurd he (List.not_mem_nil)

/-- `NetOk` of a concatenation. -/
theorem netOk_append (N : NetEnv V) (t u : List (XEvent V)) :
    NetOk N (t ++ u) ↔ NetOk N t ∧ NetOk N u := by
  simp only [NetOk, sockPart_append, List.mem_append]
  exact ⟨fun h => ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩,
    fun h e he => he.elim (h.1 e) (h.2 e)⟩

/-- The lifted predicate after embedded events. -/
theorem liftA_append (A : List Event → Prop) (evs : List Event) :
    (fun tr => liftA (V := V) A (liftT evs ++ tr)) = liftA (fun tr => A (evs ++ tr)) := by
  funext tr
  simp [liftA, lpsPart_append, lpsPart_liftT]

/-- The lifted frame exits at a lifted predicate. -/
theorem liftQ_liftA {Model : Type} (Q : MState → Model → (List Event → Prop) → Prop) (m : MState)
    (e : Model) (A : List Event → Prop) : liftQ (V := V) Q m e (liftA A) = Q m e A := by
  have h : (fun t => liftA (V := V) A (liftT t)) = A := by
    funext t
    simp [liftA, lpsPart_liftT]
  simp only [liftQ, h]

/-! ## Transport of `IoSafeN` -/

/-- Answers of a lifted environment are lifted answers. -/
theorem forall_lift_arm {E : SysEnv} {s : X86State} {e : E.Model}
    {P : XIoOut E.Model V → Prop} :
    (∀ o, (SysEnv.lift (V := V) E).arm s e o → P o) ↔ ∀ o', E.arm s e o' → P (IoOut.lift o') :=
  ⟨fun h o' ho' => h _ ⟨o', ho', rfl⟩, fun h _ ⟨o', ho', hoo⟩ => hoo ▸ h o' ho'⟩

/-- **The embedding preserves and reflects `IoSafeN`.** -/
theorem xioSafe_lift_iff {step : MState → Option MState} {E : SysEnv}
    {Q : MState → E.Model → (List Event → Prop) → Prop} :
    ∀ (n : Nat) (m : MState) (e : E.Model) (A : List Event → Prop),
      XIoSafeN (V := V) step (SysEnv.lift E) (liftQ Q) n m e (liftA A) ↔
        IoSafeN step E Q n m e A
  | 0, _, _, _ => by simp [XIoSafeN, IoSafeN]
  | n + 1, m, e, A => by
    have hnext : ∀ o : IoOut E.Model,
        (IoOut.lift (V := V) o).Next (XIoSafeN step (SysEnv.lift E) (liftQ Q) n) (liftA A) ↔
          o.Next (IoSafeN step E Q n) A := fun o => by
      cases o with
      | resume m' e' evs =>
        show XIoSafeN step (SysEnv.lift E) (liftQ Q) n m' e'
            (fun tr => liftA A (liftT evs ++ tr)) ↔ _
        rw [liftA_append]
        exact xioSafe_lift_iff n m' e' _
      | halt evs =>
        show liftA A (liftT evs) ↔ A evs
        simp only [liftA, lpsPart_liftT]
    have hrec : ∀ m', XIoSafeN (V := V) step (SysEnv.lift E) (liftQ Q) n m' e (liftA A) ↔
        IoSafeN step E Q n m' e A := fun m' => xioSafe_lift_iff n m' e A
    simp only [XIoSafeN, IoSafeN]
    refine and_congr Iff.rfl (or_congr (Iff.of_eq (liftQ_liftA (V := V) (Model := E.Model) Q m e A)) (or_congr
      (exists_congr fun m' => and_congr Iff.rfl (hrec m'))
      (and_congr Iff.rfl (forall_congr' fun ch => and_congr Iff.rfl ?_))))
    exact forall_lift_arm.trans (forall_congr' fun o => imp_congr_right fun _ => hnext o)

/-- **LPS soundness transported along the embedding.** -/
theorem xioSafe_psafe {oracle : Oracle} {nstep : NStep} {c : MState → Option MState}
    {segs : List Segment} {refused : RefusalFilter} {E : SysEnv}
    {Q : MState → E.Model → (List Event → Prop) → Prop} (hM : Agrees nstep c)
    (hS : Sound E segs refused)
    (hQ : ∀ (c' : Config (flagMachine oracle nstep)) m' e' (A' : List Event → Prop),
      AlignedF c' m' → E.Abs e' c'.model → Q m' e' A' → PSafeF segs refused A' c')
    {A : List Event → Prop} {cfg : Config (flagMachine oracle nstep)} {m : MState}
    {e : E.Model} (al : AlignedF cfg m) (he : E.Abs e cfg.model)
    (h : ∀ n, XIoSafeN (V := V) c (SysEnv.lift E) (liftQ Q) n m e (liftA A)) :
    PSafeF segs refused A cfg :=
  Silmaril.Proofs.Machine.Process.IoSpec.ioSafe_psafe hM hS hQ al he fun n =>
    (xioSafe_lift_iff n m e A).1 (h n)

/-! ## Socket syscalls -/

/-- The events of an extended answer. -/
def XIoOut.evs {Model : Type} : XIoOut Model V → List (XEvent V)
  | .resume _ _ evs => evs
  | .halt evs => evs

/-- The events of a lifted answer are embedded. -/
theorem lift_evs {Model : Type} (o : IoOut Model) :
    ∃ t, (IoOut.lift (V := V) o).evs = liftT t := by
  cases o with
  | resume m e evs => exact ⟨evs, rfl⟩
  | halt evs => exact ⟨evs, rfl⟩

/-- **Every answer of `withNet E N H` is admitted by the network.** -/
theorem withNet_arm_netOk {E : SysEnv} {N : NetEnv V} {H : X86State → E.Model → Prop}
    {s : X86State} {e : E.Model} {o : XIoOut E.Model V} (h : (withNet E N H).arm s e o) :
    NetOk N o.evs := by
  rcases h with ⟨o', -, rfl⟩ | ⟨-, m', evs, rfl, hevs⟩
  · obtain ⟨t, ht⟩ := lift_evs (V := V) o'
    rw [ht]
    exact netOk_liftT N t
  · intro ev hev
    have hev' : ev ∈ evs := by simpa [XIoOut.evs, sockPart_map_sock] using hev
    exact hevs ev hev'

/-- The answers of `E` are answers of `withNet E N H`. -/
theorem withNet_lift_arm {E : SysEnv} (N : NetEnv V) (H : X86State → E.Model → Prop)
    {s : X86State} {e : E.Model} {o : IoOut E.Model} (h : E.arm s e o) :
    (withNet E N H).arm s e (IoOut.lift o) :=
  Or.inl ⟨o, h, rfl⟩

end Silmaril.Machine.Process.IoSpecNet
