module

public import Silmaril.Proofs.Wasm.Models.FXAsyncBack.Decomp

/-!
# Inversion of `StepFX'` under contexts

A step of `E.plug X` is a step of `X` lifted through `E`, when

* the context is **isolated** (`Iso`): every value prefix of `E` sits in front of a label, frame
  or handler, never directly in front of the hole, so no rule can take operands of `X` from `E`;
* the code is **quiet** (`Quiet`): its deep focus (`Deep`, the first non-value, entering labels,
  frames and handlers) is not a branch, `return`, trap, `throw_ref`, `suspend` or `switch`, so
  no rule of a frame of `E` fires instead.

Results: `deep_unique` (the deep focus is unique), `deep_plug`, the inversions `wrap_inv` of a
head step at a label, frame or handler around quiet code, **`step_plug_inv`** (inversion under an
isolated context), and `local_inv` (a step of `fvals V ++ e :: T` is a head step at `e`).

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncBack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Proofs.Wasm.Models.FXVRuns (fval? fvals_append fvals_nil fvals_cons fval?_toAdmin
  fvals_append_cons_inj fnvF fnvF_fvals_append fnvF_cons_none)
open Silmaril.Wasm.SingleThreaded.Det (noHost Head)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX}

/-! ## The deep focus -/

/-- A label, frame or handler. -/
def IsWrap : AdminFX → Prop
  | .label .. | .frame .. | .handler .. => True
  | _ => False

/-- `e` is the first non-value of the code, entering labels, frames and handlers. -/
inductive Deep (e : AdminFX) : List AdminFX → Prop where
  | here {V : List FVal} {T : List AdminFX} (he : fval? e = none) (hw : ¬ IsWrap e) :
      Deep e (fvals V ++ e :: T)
  | label {V : List FVal} {T : List AdminFX} {n : Nat} {k : List InstrFX} {b : List AdminFX}
      (h : Deep e b) : Deep e (fvals V ++ .label n k b :: T)
  | frame {V : List FVal} {T : List AdminFX} {n : Nat} {fi : Frame} {b : List AdminFX}
      (h : Deep e b) : Deep e (fvals V ++ .frame n fi b :: T)
  | handler {V : List FVal} {T : List AdminFX} {hs : List HClause} {b : List AdminFX}
      (h : Deep e b) : Deep e (fvals V ++ .handler hs b :: T)

/-- A first non-value at which no label, frame or handler rule fires. -/
def SCalm : AdminFX → Prop
  | .core (.plain (.br _)) => False
  | .core (.plain .return_) => False
  | .core .trap => False
  | .core (.plain .throwRef) => False
  | _ => True

/-- A deep focus at which no handler rule fires. -/
def DCalm : AdminFX → Prop
  | .fx (.suspend _) => False
  | .fx (.switch _ _) => False
  | _ => True

/-- **Quiet code**: its first non-value is calm, and so is its deep focus, if any. -/
def Quiet (X : List AdminFX) : Prop :=
  (∃ V a T, X = fvals V ++ a :: T ∧ fval? a = none ∧ SCalm a) ∧ ∀ e, Deep e X → DCalm e

/-- Inversion of `Deep` at a known first non-value. -/
theorem deep_inv {e a : AdminFX} {L : List AdminFX} {V : List FVal} {T : List AdminFX}
    (h : Deep e L) (hL : L = fvals V ++ a :: T) (ha : fval? a = none) :
    (a = e ∧ ¬ IsWrap e) ∨ (∃ n k b, a = .label n k b ∧ Deep e b) ∨
      (∃ n fi b, a = .frame n fi b ∧ Deep e b) ∨ (∃ hs b, a = .handler hs b ∧ Deep e b) := by
  cases h with
  | here he hw => exact Or.inl ⟨(fvals_append_cons_inj hL he ha).2.1.symm, hw⟩
  | label h => exact Or.inr (Or.inl ⟨_, _, _, (fvals_append_cons_inj hL rfl ha).2.1.symm, h⟩)
  | frame h => exact Or.inr (Or.inr (Or.inl ⟨_, _, _, (fvals_append_cons_inj hL rfl ha).2.1.symm, h⟩))
  | handler h => exact Or.inr (Or.inr (Or.inr ⟨_, _, (fvals_append_cons_inj hL rfl ha).2.1.symm, h⟩))

theorem deep_unique_here {e e' : AdminFX} {V : List FVal} {T : List AdminFX}
    (he : fval? e = none) (hw : ¬ IsWrap e) (h' : Deep e' (fvals V ++ e :: T)) : e = e' := by
  rcases deep_inv h' rfl he with ⟨h1, -⟩ | ⟨_, _, _, h1, -⟩ | ⟨_, _, _, h1, -⟩ | ⟨_, _, h1, -⟩
  · exact h1
  all_goals exact absurd (h1 ▸ trivial) hw

theorem deep_label_inner {x : AdminFX} {V : List FVal} {n : Nat} {k : List InstrFX}
    {b T : List AdminFX} (h : Deep x (fvals V ++ .label n k b :: T)) : Deep x b := by
  rcases deep_inv h rfl rfl with ⟨he, hw⟩ | ⟨_, _, _, he, hb⟩ | ⟨_, _, _, he, -⟩ | ⟨_, _, he, -⟩
  · exact absurd (he ▸ trivial) hw
  · injection he with _ _ he; exact he ▸ hb
  · cases he
  · cases he

theorem deep_frame_inner {x : AdminFX} {V : List FVal} {n : Nat} {fi : Frame}
    {b T : List AdminFX} (h : Deep x (fvals V ++ .frame n fi b :: T)) : Deep x b := by
  rcases deep_inv h rfl rfl with ⟨he, hw⟩ | ⟨_, _, _, he, -⟩ | ⟨_, _, _, he, hb⟩ | ⟨_, _, he, -⟩
  · exact absurd (he ▸ trivial) hw
  · cases he
  · injection he with _ _ he; exact he ▸ hb
  · cases he

theorem deep_handler_inner {x : AdminFX} {V : List FVal} {hs : List HClause}
    {b T : List AdminFX} (h : Deep x (fvals V ++ .handler hs b :: T)) : Deep x b := by
  rcases deep_inv h rfl rfl with ⟨he, hw⟩ | ⟨_, _, _, he, -⟩ | ⟨_, _, _, he, -⟩ | ⟨_, _, he, hb⟩
  · exact absurd (he ▸ trivial) hw
  · cases he
  · cases he
  · injection he with _ he; exact he ▸ hb

theorem deep_unique {e e' : AdminFX} {L : List AdminFX} (h : Deep e L) (h' : Deep e' L) :
    e = e' := by
  induction h generalizing e' with
  | here he hw => exact deep_unique_here he hw h'
  | label _ ih => exact ih (deep_label_inner h')
  | frame _ ih => exact ih (deep_frame_inner h')
  | handler _ ih => exact ih (deep_handler_inner h')

theorem fvals_ne_cons {V W : List FVal} {e : AdminFX} {T : List AdminFX} (he : fval? e = none) :
    fvals V ≠ fvals W ++ e :: T := by
  intro h
  have h' := congrArg (fun l => (fnvF l).2) h
  simp [fnvF_fvals_append, fnvF_cons_none he] at h'

theorem deep_head {e : AdminFX} {L : List AdminFX} (h : Deep e L) :
    ∃ V a T, L = fvals V ++ a :: T ∧ fval? a = none := by
  cases h with
  | here he _ => exact ⟨_, _, _, rfl, he⟩
  | label _ => exact ⟨_, _, _, rfl, rfl⟩
  | frame _ => exact ⟨_, _, _, rfl, rfl⟩
  | handler _ => exact ⟨_, _, _, rfl, rfl⟩

theorem not_deep_fvals {e : AdminFX} {V : List FVal} : ¬ Deep e (fvals V) := by
  intro h
  obtain ⟨W, a, T, hc, ha⟩ := deep_head h
  exact fvals_ne_cons ha hc

theorem deep_seq {e : AdminFX} {L : List AdminFX} (h : Deep e L) (vs : List FVal)
    (rest : List AdminFX) : Deep e (fvals vs ++ L ++ rest) := by
  cases h with
  | here he hw => simpa using Deep.here (V := vs ++ _) (T := _ ++ rest) he hw
  | label h => simpa using Deep.label (V := vs ++ _) (T := _ ++ rest) h
  | frame h => simpa using Deep.frame (V := vs ++ _) (T := _ ++ rest) h
  | handler h => simpa using Deep.handler (V := vs ++ _) (T := _ ++ rest) h

theorem deep_plug {e : AdminFX} {X : List AdminFX} (h : Deep e X) (E : CtxV) :
    Deep e (E.plug X) := by
  induction E with
  | hole => exact h
  | seq vs E rest ih => exact deep_seq ih vs rest
  | label n k E ih => exact Deep.label (V := []) (T := []) ih
  | frame n f E ih => exact Deep.frame (V := []) (T := []) ih
  | handler hs E ih => exact Deep.handler (V := []) (T := []) ih

/-- `Deep` through a value prefix and a suffix, at code with a non-value. -/
theorem deep_seq_inv {e : AdminFX} {L : List AdminFX} {vs : List FVal} {rest : List AdminFX}
    (hL : ∃ V a T, L = fvals V ++ a :: T ∧ fval? a = none) (h : Deep e (fvals vs ++ L ++ rest)) :
    Deep e L := by
  obtain ⟨V, a, T, rfl, ha⟩ := hL
  have hc : fvals vs ++ (fvals V ++ a :: T) ++ rest = fvals (vs ++ V) ++ a :: (T ++ rest) := by
    simp
  rw [hc] at h
  rcases deep_inv h rfl ha with ⟨rfl, hw⟩ | ⟨n, k, b, rfl, hb⟩ | ⟨n, fi, b, rfl, hb⟩ |
      ⟨hs, b, rfl, hb⟩
  · exact Deep.here ha hw
  · exact Deep.label hb
  · exact Deep.frame hb
  · exact Deep.handler hb

theorem plug_head (E : CtxV) {X : List AdminFX} (hX : ∃ V a T, X = fvals V ++ a :: T ∧ fval? a = none) :
    ∃ V a T, E.plug X = fvals V ++ a :: T ∧ fval? a = none := by
  induction E with
  | hole => exact hX
  | seq vs E rest ih =>
    obtain ⟨V, a, T, hc, ha⟩ := ih
    exact ⟨vs ++ V, a, T ++ rest, by simp [CtxV.plug, hc], ha⟩
  | label n k E _ => exact ⟨[], _, [], rfl, rfl⟩
  | frame n f E _ => exact ⟨[], _, [], rfl, rfl⟩
  | handler hs E _ => exact ⟨[], _, [], rfl, rfl⟩

theorem deep_plug_inv {e : AdminFX} {X : List AdminFX}
    (hX : ∃ V a T, X = fvals V ++ a :: T ∧ fval? a = none) :
    ∀ (E : CtxV), Deep e (E.plug X) → Deep e X
  | .hole, h => h
  | .seq vs E rest, h => deep_plug_inv hX E (deep_seq_inv (plug_head E hX) h)
  | .label n k E, h => by
    rcases deep_inv (V := []) (T := []) h rfl rfl with ⟨he, hw⟩ | ⟨_, _, _, he, hb⟩ |
        ⟨_, _, _, he, -⟩ | ⟨_, _, he, -⟩
    · subst he; exact absurd trivial hw
    · cases he; exact deep_plug_inv hX E hb
    · cases he
    · cases he
  | .frame n f E, h => by
    rcases deep_inv (V := []) (T := []) h rfl rfl with ⟨he, hw⟩ | ⟨_, _, _, he, -⟩ |
        ⟨_, _, _, he, hb⟩ | ⟨_, _, he, -⟩
    · subst he; exact absurd trivial hw
    · cases he
    · cases he; exact deep_plug_inv hX E hb
    · cases he
  | .handler hs E, h => by
    rcases deep_inv (V := []) (T := []) h rfl rfl with ⟨he, hw⟩ | ⟨_, _, _, he, -⟩ |
        ⟨_, _, _, he, -⟩ | ⟨_, _, he, hb⟩
    · subst he; exact absurd trivial hw
    · cases he
    · cases he
    · cases he; exact deep_plug_inv hX E hb

theorem quiet_ne {X : List AdminFX} {e₀ : AdminFX} (hq : Quiet X) (hd : Deep e₀ X)
    (hc : ¬ DCalm e₀) : False :=
  hc (hq.2 e₀ hd)

theorem quiet_not_fvals {V : List FVal} (hq : Quiet (fvals V)) : False := by
  obtain ⟨⟨W, a, T, h, ha, -⟩, -⟩ := hq
  exact fvals_ne_cons ha h

theorem br_code (vs' vs : List FVal) (l : LabelIdx) (rest : List AdminFX) :
    fvals vs' ++ fvals vs ++ [.core (.plain (.br l))] ++ rest =
      fvals (vs' ++ vs) ++ .core (.plain (.br l)) :: rest := by simp

theorem ret_code (vs' vs : List FVal) (rest : List AdminFX) :
    fvals vs' ++ fvals vs ++ [.core (.plain .return_)] ++ rest =
      fvals (vs' ++ vs) ++ .core (.plain .return_) :: rest := by simp

theorem throw_code (a : Nat) :
    cthrowing a = fvals [.val (.ref (.exn a))] ++ .core (.plain .throwRef) :: [] := by
  simp [cthrowing, FVal.toAdmin, Val.toAdmin]

theorem quiet_head {V : List FVal} {e₀ : AdminFX} {T : List AdminFX} {X' : List AdminFX}
    (hq : Quiet X') (hX : X' = fvals V ++ e₀ :: T) (he : fval? e₀ = none) (hc : ¬ SCalm e₀) :
    False := by
  obtain ⟨⟨V', a, T', hX', ha, hca⟩, -⟩ := hq
  rw [hX] at hX'
  obtain ⟨-, rfl, -⟩ := fvals_append_cons_inj hX' he ha
  exact hc hca

theorem deep_br {V V' : List FVal} {l : LabelIdx} {rest : List AdminFX} :
    Deep (.core (.plain (.br l))) (fvals V' ++ fvals V ++ [.core (.plain (.br l))] ++ rest) := by
  simpa using Deep.here (V := V' ++ V) (T := rest) (e := .core (.plain (.br l))) rfl id

theorem deep_ret {V V' : List FVal} {rest : List AdminFX} :
    Deep (.core (.plain .return_)) (fvals V' ++ fvals V ++ [.core (.plain .return_)] ++ rest) := by
  simpa using Deep.here (V := V' ++ V) (T := rest) (e := .core (.plain .return_)) rfl id

theorem deep_trap : Deep (.core .trap) [.core .trap] :=
  Deep.here (V := []) (T := []) rfl id

theorem deep_throw (a : Nat) : Deep (.core (.plain .throwRef)) (cthrowing a) := by
  simpa [cthrowing, FVal.toAdmin, Val.toAdmin] using
    Deep.here (V := [.val (.ref (.exn a))]) (T := []) (e := .core (.plain .throwRef)) rfl id

theorem deep_suspend (E : CtxV) (vs : List FVal) (x : TagIdx) :
    Deep (.fx (.suspend x)) (E.plug (fvals vs ++ [.fx (.suspend x)])) :=
  deep_plug (Deep.here (V := vs) (T := []) rfl id) E

theorem deep_switch (E : CtxV) (vs : List FVal) (k : Nat) (ct : TypeIdx) (x : TagIdx) :
    Deep (.fx (.switch ct x)) (E.plug (fvals vs ++ [.contRef k, .fx (.switch ct x)])) := by
  have h : fvals vs ++ [.contRef k, .fx (.switch ct x)] =
      fvals (vs ++ [.cont k]) ++ .fx (.switch ct x) :: [] := by simp [FVal.toAdmin]
  rw [h]
  exact deep_plug (Deep.here rfl id) E

/-! ## Head steps at a label, frame or handler around quiet code -/

theorem label_inv {s : Store H} {K : List (Option ContFX)} {f : Frame} {V : List FVal} {n : Nat}
    {k : List InstrFX} {b : List AdminFX} {d : ConfigFX H} (hq : Quiet b)
    (h : FHead P fx s K f V (.label n k b) d) :
    V = [] ∧ ∃ s' K' f' b', StepFX' P noHost fx ⟨s, K, f, b⟩ ⟨s', K', f', b'⟩ ∧
      d = ⟨s', K', f', [.label n k b']⟩ := by
  cases h with
  | ctxLabel h => exact ⟨rfl, _, _, _, _, h, rfl⟩
  | labelVals => exact (quiet_not_fvals hq).elim
  | brLabelZero => exact (quiet_head hq (br_code _ _ _ _) rfl id).elim
  | brLabelSucc => exact (quiet_head hq (br_code [] _ _ _) rfl id).elim
  | returnLabel => exact (quiet_head hq (ret_code [] _ _) rfl id).elim
  | trapLabel => exact (quiet_head hq (V := []) (T := []) rfl rfl id).elim
  | throwLabel => exact (quiet_head hq (throw_code _) rfl id).elim

theorem frame_inv {s : Store H} {K : List (Option ContFX)} {f : Frame} {V : List FVal} {n : Nat}
    {fi : Frame} {b : List AdminFX} {d : ConfigFX H} (hq : Quiet b)
    (h : FHead P fx s K f V (.frame n fi b) d) :
    V = [] ∧ ∃ s' K' fi' b', StepFX' P noHost fx ⟨s, K, fi, b⟩ ⟨s', K', fi', b'⟩ ∧
      d = ⟨s', K', f, [.frame n fi' b']⟩ := by
  cases h with
  | ctxFrame h => exact ⟨rfl, _, _, _, _, h, rfl⟩
  | frameVals => exact (quiet_not_fvals hq).elim
  | returnFrame => exact (quiet_head hq (ret_code _ _ _) rfl id).elim
  | trapFrame => exact (quiet_head hq (V := []) (T := []) rfl rfl id).elim
  | throwFrame => exact (quiet_head hq (throw_code _) rfl id).elim

theorem handler_inv {s : Store H} {K : List (Option ContFX)} {f : Frame} {V : List FVal}
    {hs : List HClause} {b : List AdminFX} {d : ConfigFX H} (hq : Quiet b)
    (h : FHead P fx s K f V (.handler hs b) d) :
    V = [] ∧ ∃ s' K' f' b', StepFX' P noHost fx ⟨s, K, f, b⟩ ⟨s', K', f', b'⟩ ∧
      d = ⟨s', K', f', [.handler hs b']⟩ := by
  cases h with
  | ctxHandler h => exact ⟨rfl, _, _, _, _, h, rfl⟩
  | handlerVals => exact (quiet_not_fvals hq).elim
  | brHandler => exact (quiet_head hq (br_code [] _ _ _) rfl id).elim
  | returnHandler => exact (quiet_head hq (ret_code [] _ _) rfl id).elim
  | trapHandler => exact (quiet_head hq (V := []) (T := []) rfl rfl id).elim
  | throwHandler => exact (quiet_head hq (throw_code _) rfl id).elim
  | suspend => exact (quiet_ne hq (deep_suspend _ _ _) id).elim
  | switch => exact (quiet_ne hq (deep_switch _ _ _ _ _) id).elim

/-! ## Steps at the first non-value -/

/-- **A step of `fvals V ++ e :: T`** at a non-value other than a trap or `throw_ref` is a head
step at `e`, with a suffix `V₂` of `V`. -/
theorem local_inv {s : Store H} {K : List (Option ContFX)} {f : Frame} {V : List FVal}
    {e : AdminFX} {T : List AdminFX} {d : ConfigFX H} (he : fval? e = none)
    (ht : e ≠ .core .trap) (hr : e ≠ .core (.plain .throwRef))
    (h : StepFX' P noHost fx ⟨s, K, f, fvals V ++ e :: T⟩ d) :
    ∃ V₁ V₂ d₀, V = V₁ ++ V₂ ∧ FHead P fx s K f V₂ e d₀ ∧
      d = ⟨d₀.store, d₀.conts, d₀.frame, fvals V₁ ++ d₀.code ++ T⟩ := by
  rcases stepFX'_decomp h with ⟨V₁, V₂, e', T', d₀, hc, he', hh, rfl⟩ | ⟨W, T', hb | hb⟩
  · have hc' : fvals V ++ e :: T = fvals (V₁ ++ V₂) ++ e' :: T' := by simpa using hc
    obtain ⟨rfl, rfl, rfl⟩ := fvals_append_cons_inj hc' he he'
    exact ⟨V₁, V₂, d₀, rfl, hh, rfl⟩
  · exact absurd (fvals_append_cons_inj hb he rfl).2.1 ht
  · exact absurd (fvals_append_cons_inj hb he rfl).2.1 hr

/-! ## Isolated contexts -/

/-- **Isolated contexts**: a value prefix is never directly in front of the hole. -/
def Iso : CtxV → Prop
  | .hole => True
  | .seq _ (.label _ _ E) _ => Iso E
  | .seq _ (.frame _ _ E) _ => Iso E
  | .seq _ (.handler _ E) _ => Iso E
  | .seq _ _ _ => False
  | .label _ _ E => Iso E
  | .frame _ _ E => Iso E
  | .handler _ E => Iso E

theorem quiet_plug {X : List AdminFX} (hq : Quiet X) : ∀ (E : CtxV), Iso E → Quiet (E.plug X)
  | .hole, _ => hq
  | .seq vs (.label n k E) rest, _ =>
    ⟨⟨vs, .label n k (E.plug X), rest, by simp [CtxV.plug], rfl, trivial⟩, fun e hd =>
      hq.2 e (deep_plug_inv (let ⟨V, a, T, h, ha, _⟩ := hq.1; ⟨V, a, T, h, ha⟩) _ hd)⟩
  | .seq vs (.frame n f E) rest, _ =>
    ⟨⟨vs, .frame n f (E.plug X), rest, by simp [CtxV.plug], rfl, trivial⟩, fun e hd =>
      hq.2 e (deep_plug_inv (let ⟨V, a, T, h, ha, _⟩ := hq.1; ⟨V, a, T, h, ha⟩) _ hd)⟩
  | .seq vs (.handler hs E) rest, _ =>
    ⟨⟨vs, .handler hs (E.plug X), rest, by simp [CtxV.plug], rfl, trivial⟩, fun e hd =>
      hq.2 e (deep_plug_inv (let ⟨V, a, T, h, ha, _⟩ := hq.1; ⟨V, a, T, h, ha⟩) _ hd)⟩
  | .label n k E, _ =>
    ⟨⟨[], .label n k (E.plug X), [], rfl, rfl, trivial⟩, fun e hd =>
      hq.2 e (deep_plug_inv (let ⟨V, a, T, h, ha, _⟩ := hq.1; ⟨V, a, T, h, ha⟩) _ hd)⟩
  | .frame n f E, _ =>
    ⟨⟨[], .frame n f (E.plug X), [], rfl, rfl, trivial⟩, fun e hd =>
      hq.2 e (deep_plug_inv (let ⟨V, a, T, h, ha, _⟩ := hq.1; ⟨V, a, T, h, ha⟩) _ hd)⟩
  | .handler hs E, _ =>
    ⟨⟨[], .handler hs (E.plug X), [], rfl, rfl, trivial⟩, fun e hd =>
      hq.2 e (deep_plug_inv (let ⟨V, a, T, h, ha, _⟩ := hq.1; ⟨V, a, T, h, ha⟩) _ hd)⟩

/-- Lift a configuration at the hole of a context back to the plugged code. -/
def liftC : CtxV → Frame → ConfigFX H → ConfigFX H
  | .hole, _, c => c
  | .seq vs E rest, f, c =>
    let r := liftC E f c
    ⟨r.store, r.conts, r.frame, fvals vs ++ r.code ++ rest⟩
  | .label n k E, f, c =>
    let r := liftC E f c
    ⟨r.store, r.conts, r.frame, [.label n k r.code]⟩
  | .frame n fi E, f, c =>
    let r := liftC E fi c
    ⟨r.store, r.conts, f, [.frame n r.frame r.code]⟩
  | .handler hs E, f, c =>
    let r := liftC E f c
    ⟨r.store, r.conts, r.frame, [.handler hs r.code]⟩

theorem liftC_frameAt (E : CtxV) (f : Frame) (s : Store H) (K : List (Option ContFX))
    (X : List AdminFX) : liftC E f ⟨s, K, E.frameAt f, X⟩ = ⟨s, K, f, E.plug X⟩ := by
  induction E generalizing f with
  | hole => rfl
  | seq vs E rest ih => simp only [liftC, CtxV.frameAt, ih, CtxV.plug]
  | label n k E ih => simp only [liftC, CtxV.frameAt, ih, CtxV.plug]
  | frame n fi E ih => simp only [liftC, CtxV.frameAt, ih, CtxV.plug]
  | handler hs E ih => simp only [liftC, CtxV.frameAt, ih, CtxV.plug]

/-- The goal of `step_plug_inv`. -/
def PlugInv (P : Profile) (fx : H → Option FuncFX) (E : CtxV) (X : List AdminFX) : Prop :=
  ∀ (s : Store H) (K : List (Option ContFX)) (f : Frame) (d : ConfigFX H),
    StepFX' P noHost fx ⟨s, K, f, E.plug X⟩ d →
      ∃ c', StepFX' P noHost fx ⟨s, K, E.frameAt f, X⟩ c' ∧ d = liftC E f c'

theorem wrapper_head {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal}
    {w : AdminFX} {rest : List AdminFX} {d : ConfigFX H} (hw : fval? w = none)
    (ht : w ≠ .core .trap) (hr : w ≠ .core (.plain .throwRef))
    (h : StepFX' P noHost fx ⟨s, K, f, fvals vs ++ w :: rest⟩ d) :
    ∃ V₁ V₂ d₀, vs = V₁ ++ V₂ ∧ FHead P fx s K f V₂ w d₀ ∧
      d = ⟨d₀.store, d₀.conts, d₀.frame, fvals V₁ ++ d₀.code ++ rest⟩ :=
  local_inv hw ht hr h

theorem plugInv_label {n : Nat} {k : List InstrFX} {E : CtxV} {X : List AdminFX} (hq : Quiet X)
    (hE : Iso E) (ih : PlugInv P fx E X) (vs : List FVal) (rest : List AdminFX) :
    PlugInv P fx (.seq vs (.label n k E) rest) X := by
  intro s K f d h
  obtain ⟨V₁, V₂, d₀, rfl, hh, rfl⟩ :=
    wrapper_head (w := .label n k (E.plug X)) rfl (by simp) (by simp) (by simpa [CtxV.plug] using h)
  obtain ⟨rfl, s', K', f', b', hb, rfl⟩ := label_inv (quiet_plug hq E hE) hh
  obtain ⟨c', hc', hd⟩ := ih s K f _ hb
  refine ⟨c', hc', ?_⟩
  simp only [liftC, ← hd, List.append_nil]

theorem plugInv_frame {n : Nat} {fi : Frame} {E : CtxV} {X : List AdminFX} (hq : Quiet X)
    (hE : Iso E) (ih : PlugInv P fx E X) (vs : List FVal) (rest : List AdminFX) :
    PlugInv P fx (.seq vs (.frame n fi E) rest) X := by
  intro s K f d h
  obtain ⟨V₁, V₂, d₀, rfl, hh, rfl⟩ :=
    wrapper_head (w := .frame n fi (E.plug X)) rfl (by simp) (by simp) (by simpa [CtxV.plug] using h)
  obtain ⟨rfl, s', K', fi', b', hb, rfl⟩ := frame_inv (quiet_plug hq E hE) hh
  obtain ⟨c', hc', hd⟩ := ih s K fi _ hb
  refine ⟨c', hc', ?_⟩
  simp only [liftC, ← hd, List.append_nil]

theorem plugInv_handler {hs : List HClause} {E : CtxV} {X : List AdminFX} (hq : Quiet X)
    (hE : Iso E) (ih : PlugInv P fx E X) (vs : List FVal) (rest : List AdminFX) :
    PlugInv P fx (.seq vs (.handler hs E) rest) X := by
  intro s K f d h
  obtain ⟨V₁, V₂, d₀, rfl, hh, rfl⟩ :=
    wrapper_head (w := .handler hs (E.plug X)) rfl (by simp) (by simp) (by simpa [CtxV.plug] using h)
  obtain ⟨rfl, s', K', f', b', hb, rfl⟩ := handler_inv (quiet_plug hq E hE) hh
  obtain ⟨c', hc', hd⟩ := ih s K f _ hb
  refine ⟨c', hc', ?_⟩
  simp only [liftC, ← hd, List.append_nil]

/-- A wrapper alone is a wrapper under an empty sequence. -/
theorem plugInv_bare {E : CtxV} {X : List AdminFX} (h : PlugInv P fx (.seq [] E []) X) :
    PlugInv P fx E X := by
  intro s K f d hs
  obtain ⟨c', hc', hd⟩ := h s K f d (by simpa [CtxV.plug] using hs)
  refine ⟨c', by simpa [CtxV.frameAt] using hc', ?_⟩
  rw [hd]
  simp only [liftC, fvals_nil, List.nil_append, List.append_nil]

/-- **Inversion under an isolated context**: a step of `E.plug X`, for quiet `X`, is a step of
`X` at the frame of the hole, lifted through `E`. -/
theorem step_plug_inv {X : List AdminFX} (hq : Quiet X) :
    ∀ (E : CtxV), Iso E → PlugInv P fx E X
  | .hole, _ => fun _ _ _ _ h => ⟨_, h, rfl⟩
  | .seq vs (.label _ _ E) rest, hE => plugInv_label (E := E) hq hE (step_plug_inv hq E hE) vs rest
  | .seq vs (.frame _ _ E) rest, hE => plugInv_frame (E := E) hq hE (step_plug_inv hq E hE) vs rest
  | .seq vs (.handler _ E) rest, hE => plugInv_handler (E := E) hq hE (step_plug_inv hq E hE) vs rest
  | .label _ _ E, hE => plugInv_bare (plugInv_label (E := E) hq hE (step_plug_inv hq E hE) [] [])
  | .frame _ _ E, hE => plugInv_bare (plugInv_frame (E := E) hq hE (step_plug_inv hq E hE) [] [])
  | .handler _ E, hE => plugInv_bare (plugInv_handler (E := E) hq hE (step_plug_inv hq E hE) [] [])

end Silmaril.Proofs.Wasm.Models.FXAsyncBack
