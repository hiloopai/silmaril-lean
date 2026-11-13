module

public import Silmaril.Wasi.Versions.P2OverP3.Fs.Defs
public import Silmaril.Proofs.Wasi.Versions.P2OverP3.Leaves

/-!
# Proofs: results and calls of sanitized programs; frames of the 0.3 theories

* `LeavesC C p P`: every call of `p` satisfies `C` and every result satisfies `P`, whatever the
  answers. `Wp.of_leavesC`: then a predicate on the theory state preserved by every accepted
  answer to a call satisfying `C` holds at the end. `leavesC_san`: a sanitized program makes no
  ruled-out call, and its results are results of the original program.
* `rest_setRest`, `rd3_frame`, `rd3_keep`: the loose 0.3 read theory changes the rest of a
  readable end only on a `stream.read` of that end or a `read-via-stream` answer;
  `t3_step`: the steps of the product `t3F F`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P3
open Silmaril.Wasi.Versions.P3OverP2 (fsReadTh3w rdShaped rdStepZ)

/-! ## Results and calls -/

/-- Every call satisfies `C` and every result satisfies `P`, whatever the answers. -/
def LeavesC {A : Type} (C : FnName → List Val → Prop) : PgF A → (A → Prop) → Prop
  | .pure a, P => P a
  | .call m k, P => C m.1.1 m.2 ∧ ∀ n, LeavesC C (k n) P

variable {A B : Type} {C : FnName → List Val → Prop}

theorem LeavesC.mono {P Q : A → Prop} (h : ∀ a, P a → Q a) :
    ∀ {p : PgF A}, LeavesC C p P → LeavesC C p Q
  | .pure _, hp => h _ hp
  | .call _ _, hp => ⟨hp.1, fun n => LeavesC.mono h (hp.2 n)⟩

theorem leavesC_bind {P : B → Prop} (f : A → PgF B) :
    ∀ p : PgF A, LeavesC C p (fun a => LeavesC C (f a) P) → LeavesC C (p.bind f) P
  | .pure _, h => h
  | .call _ k, h => ⟨h.1, fun n => leavesC_bind f (k n) (h.2 n)⟩

/-- **A sanitized program makes no ruled-out call**, and its results are the original's. -/
theorem leavesC_san (bad : FnName → List Val → Bool) (fake : Option (List Val)) {P : A → Prop} :
    ∀ p : Pg A, Leaves p P → LeavesC (fun f a => bad f a = false) (san bad fake p) P
  | .pure _, h => h
  | .call m k, h => by
    unfold san
    split
    · exact leavesC_san bad fake (k fake) (h fake)
    · next hb => exact ⟨Bool.of_not_eq_true hb, fun n => leavesC_san bad fake (k n) (h n)⟩

/-- **Weakest preconditions from results and calls.** -/
theorem Wp.of_leavesC {ST : Type} {T : Protocol ST WEv} {R : ST → Prop}
    (hR : ∀ q f a n q', R q → C f a → T.step q (.imp f a n) = some q' → R q') {P : A → Prop}
    {Q : A → ST → Prop} (hQ : ∀ a q, R q → P a → Q a q) :
    ∀ (p : PgF A) {qT : ST}, LeavesC C p P → R qT → Wp T p Q qT
  | .pure a, _, hp, hq => hQ a _ hq hp
  | .call _ k, _, hp, hq => fun n _ hn =>
    Wp.of_leavesC hR hQ (k n) (hp.2 n) (hR _ _ _ _ _ hq hp.1 hn)

/-! ## The read theory -/

theorem rest_setRest (q : RdSt) (r k : Nat) (bs : List (BitVec 8)) :
    rest (setRest q r bs) k = if k = r then some bs else rest q k := by
  by_cases h : k = r
  · subst h; simp [rest, setRest]
  · simp [rest, setRest, Ne.symm h, h]

/-- An accepted step of `fsReadTh3w F` on an answer to a call other than `read-via-stream` and
`stream.read` keeps the state. -/
theorem rd3_keep {F : BitVec 32 → List (BitVec 8)} {q q' : RdSt} {f : FnName} {a : List Val}
    {n : Option (List Val)} (h : (fsReadTh3w F).step q (.imp f a n) = some q')
    (h1 : f ≠ readVia3) (h2 : f ≠ cStreamRead) : q' = q := by
  have hs : (fsReadTh3w F).step q (.imp f a n) = some q := by
    show (if rdShaped (.imp f a n) then rdStepZ F q (.imp f a n) else some q) = some q
    split
    · simp [rdStepZ, h1, h2]
    · rfl
  exact Option.some.inj (h.symm.trans hs)

/-- The accepted steps of `fsReadTh3w F` on a `stream.read` answer: the state is kept, or the
rest of the end named by the arguments is set. -/
theorem rd3_read_cases {F : BitVec 32 → List (BitVec 8)} {q q' : RdSt} {a : List Val}
    {n : Option (List Val)} (h : (fsReadTh3w F).step q (.imp cStreamRead a n) = some q') :
    q' = q ∨ ∃ r v, keyOf a = some r ∧ q' = setRest q r v := by
  have h1 : cStreamRead ≠ readVia3 := by decide
  have hs : (if rdShaped (.imp cStreamRead a n) then rdStepZ F q (.imp cStreamRead a n)
      else some q) = some q' := h
  simp only [rdStepZ, ite_false, ite_true, h1] at hs
  repeat' split at hs
  all_goals first
    | (obtain ⟨r', hr', hq⟩ := Option.map_eq_some_iff.1 hs
       exact Or.inr ⟨r', _, by simp [keyOf, hr'], hq.symm⟩)
    | (cases hs; exact Or.inl rfl)
    | exact absurd hs (by simp)

/-- **The frame of the read theory**: a step on an answer to a call that is not
`read-via-stream`, nor a `stream.read` of an end in `K`, keeps the rest of every end in `K`. -/
theorem rd3_frame {F : BitVec 32 → List (BitVec 8)} {K : Nat → Prop} {q q' : RdSt} {f : FnName}
    {a : List Val} {n : Option (List Val)} (h : (fsReadTh3w F).step q (.imp f a n) = some q')
    (h1 : f ≠ readVia3) (h2 : f = cStreamRead → ∀ k, keyOf a = some k → ¬ K k) :
    ∀ k, K k → rest q' k = rest q k := by
  intro k hk
  by_cases hf : f = cStreamRead
  · subst hf
    rcases rd3_read_cases h with rfl | ⟨r, v, hr, rfl⟩
    · rfl
    · have hne : k ≠ r := fun he => h2 rfl r hr (he ▸ hk)
      rw [rest_setRest, ite_eq_right hne]
  · rw [rd3_keep h h1 hf]

/-! ## The product theory -/

theorem t3_step {F : BitVec 32 → List (BitVec 8)} {qC qC' : ClockSt} {q3 q3' : RdSt} {e : WEv}
    (h : (t3F F).step (qC, q3) e = some (qC', q3')) :
    clockStep3 qC e = some qC' ∧ (fsReadTh3w F).step q3 e = some q3' := by
  simp only [t3F, Protocol.prod, clockTh3] at h
  obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨b, hb', hab⟩ := Option.map_eq_some_iff.1 hb
  cases hab
  exact ⟨ha, hb'⟩

end Silmaril.Wasi.Versions.P2OverP3
