module

public import Silmaril.Proofs.Wasm.Wasmi.Fuse
public import Silmaril.Wasm.Execution.Core.Sim.Context

@[expose] public section

/-!
# The simulation relation from wasmi's translated code to the loose model

`LRel wL wR` relates runtime code of the translated store (left, run by Core) to runtime code
of the source store (right, run by the loose model). It is pointwise (`ARel`: identity,
related structured instructions, `LABEL`/`HANDLER`/`FRAME` with related bodies and label
continuations), with two more kinds of pairs:

* `group`: a translated pattern `local.get x; drop; i32.const 0; select t` against its source
  `i32.const 0; local.get x; i32.ne; select t`. When the left reads the local, the right takes
  the `selectEither` quirk with the constant `0`, after which both sides are equal;
* `cut`: a `trap` or `THROW_REF` followed by code of equal length on both sides. A trap or a
  throw under `ctxt-instrs` discards an arbitrary prefix of the code after it, which may end
  inside a group; the cut pairs absorb this, and the right side discards the same number of
  instructions (both sides of a group have length four, so `LRel` preserves lengths).

The simulation is in lock step: every left step is matched by exactly one loose step.

Lemmas: lengths, reflexivity, concatenation, `src` (lowering of `InstrsRel fuseBI`),
`ofAdminsRel` (silmaril-lean's closure without base pairs is contained in `LRel`), and the
inversions used by the simulation (`peel`, `cons_inv`, `ARel.*_inv`, `eq_vals`, `result_inv`).

New proofs.
-/

namespace Silmaril.Proofs.Wasm.Wasmi

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.Wasmi

mutual
/-- Related administrative instructions (left: translated, right: source). -/
inductive ARel : Admin → Admin → Prop where
  | refl (a : Admin) : ARel a a
  | plain {i j : Instr} : InstrRel fuseBI i j → ARel (.plain i) (.plain j)
  | label (n : Nat) {c c' : List Instr} {b b' : List Admin} :
      InstrsRel fuseBI c c' → LRel b b' → ARel (.label n c b) (.label n c' b')
  | handler (n : Nat) (cs : List Catch) {b b' : List Admin} :
      LRel b b' → ARel (.handler n cs b) (.handler n cs b')
  | frame (n : Nat) (fi : Frame) {b b' : List Admin} :
      LRel b b' → ARel (.frame n fi b) (.frame n fi b')

/-- Related runtime code (left: translated, right: source). -/
inductive LRel : List Admin → List Admin → Prop where
  | nil : LRel [] []
  | cons {a b : Admin} {l r : List Admin} : ARel a b → LRel l r → LRel (a :: l) (b :: r)
  | group (x : LocalIdx) (t : Option (List ValType)) {l r : List Admin} : LRel l r →
      LRel (expression (fusedSel x t) ++ l) (expression (zeroTestSel x t) ++ r)
  | cut {k : Admin} (hk : k = .trap ∨ k = .plain .throwRef) {l r : List Admin} :
      l.length = r.length → LRel (k :: l) (k :: r)
end

/-! ## Structure -/

theorem LRel.length : ∀ {l r : List Admin}, LRel l r → l.length = r.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [h.length]
  | _, _, .group _ _ h => by simp [expression, fusedSel, zeroTestSel, h.length]
  | _, _, .cut _ h => by simp [h]

theorem LRel.refl : ∀ l : List Admin, LRel l l
  | [] => .nil
  | a :: l => .cons (.refl a) (LRel.refl l)

theorem LRel.append : ∀ {a b c d : List Admin}, LRel a b → LRel c d → LRel (a ++ c) (b ++ d)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h₁ h₂, h => .cons h₁ (h₂.append h)
  | _, _, _, _, .group x t h₁, h => by
    rw [List.append_assoc, List.append_assoc]; exact .group x t (h₁.append h)
  | _, _, _, _, .cut hk h₁, h => .cut hk (by simp [h₁, h.length])

theorem LRel.vals_append (vs : List Val) {l r : List Admin} (h : LRel l r) :
    LRel (vals vs ++ l) (vals vs ++ r) :=
  (LRel.refl _).append h

/-- Lowering related source sequences. -/
theorem LRel.src : ∀ {x y : List Instr}, InstrsRel fuseBI x y →
    LRel (expression x) (expression y)
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (.plain h) (LRel.src t)
  | _, _, .base ⟨x, t, h₁, h₂⟩ => by
    subst h₁ h₂; simpa using LRel.group x t .nil
  | _, _, .append h₁ h₂ => by
    simp only [expression, List.map_append]; exact (LRel.src h₁).append (LRel.src h₂)

mutual
/-- silmaril-lean's closure without base pairs is contained in `ARel`. -/
theorem ARel.ofAdminRel : ∀ {a b : Admin}, AdminRel fuseBI (fun _ _ => False) a b → ARel a b
  | _, _, .refl a => .refl a
  | _, _, .plain h => .plain h
  | _, _, .label n hc hb => .label n hc (LRel.ofAdminsRel hb)
  | _, _, .handler n cs hb => .handler n cs (LRel.ofAdminsRel hb)
  | _, _, .frame n f hb => .frame n f (LRel.ofAdminsRel hb)

/-- silmaril-lean's closure without base pairs is contained in `LRel`. -/
theorem LRel.ofAdminsRel : ∀ {x y : List Admin},
    AdminsRel fuseBI (fun _ _ => False) x y → LRel x y
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (ARel.ofAdminRel h) (LRel.ofAdminsRel t)
  | _, _, .base h => h.elim
  | _, _, .src h => LRel.src h
  | _, _, .append h t => (LRel.ofAdminsRel h).append (LRel.ofAdminsRel t)
end

/-! ## Inversions -/

/-- An administrative instruction without nested code: not structured, not a context. -/
def Flat : Admin → Prop
  | .plain (.block ..) | .plain (.loop ..) | .plain (.if_ ..) | .plain (.tryTable ..) => False
  | .label .. | .handler .. | .frame .. => False
  | _ => True

/-- A flat instruction is related only to itself. -/
theorem ARel.eq_of_flat {a b : Admin} (h : ARel a b) (ha : Flat a) : b = a := by
  cases h with
  | refl => rfl
  | plain hi => cases hi <;> first | rfl | exact (ha : False).elim
  | label => exact (ha : False).elim
  | handler => exact (ha : False).elim
  | frame => exact (ha : False).elim

theorem flat_toAdmin (v : Val) : Flat v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> trivial

theorem toAdmin_ne_localGet (v : Val) (x : LocalIdx) : v.toAdmin ≠ .plain (.localGet x) := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin]

theorem toAdmin_ne_trap (v : Val) : v.toAdmin ≠ .trap ∧ v.toAdmin ≠ .plain .throwRef := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin]

/-- **Inversion at a head.** -/
theorem LRel.cons_inv {a : Admin} {es R : List Admin} (h : LRel (a :: es) R) :
    (∃ b r, R = b :: r ∧ ARel a b ∧ LRel es r) ∨
    (∃ x t l r, a = .plain (.localGet x) ∧
      es = [.plain .drop, .plain (.intConst .i32 0), .plain (.select t)] ++ l ∧
      R = expression (zeroTestSel x t) ++ r ∧ LRel l r) ∨
    ((a = .trap ∨ a = .plain .throwRef) ∧ ∃ r, R = a :: r ∧ es.length = r.length) := by
  generalize hw : a :: es = w at h
  cases h with
  | nil => cases hw
  | cons hab hl =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hw
    exact Or.inl ⟨_, _, rfl, hab, hl⟩
  | group x t hl =>
    simp only [expression, fusedSel, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.cons.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact Or.inr (Or.inl ⟨x, t, _, _, rfl, rfl, rfl, hl⟩)
  | cut hk hl =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hw
    exact Or.inr (Or.inr ⟨hk, _, rfl, hl⟩)

/-- At a `trap` or `THROW_REF` head, the right side has the same head and a tail of the same
length. -/
theorem LRel.kernel_inv {a : Admin} {es R : List Admin} (h : LRel (a :: es) R)
    (ha : a = .trap ∨ a = .plain .throwRef) : ∃ r, R = a :: r ∧ es.length = r.length := by
  rcases h.cons_inv with ⟨b, r, rfl, hab, hl⟩ | ⟨x, t, l, r, rfl, -⟩ | ⟨-, hr⟩
  · have hf : Flat a := by rcases ha with rfl | rfl <;> trivial
    exact ⟨r, by rw [hab.eq_of_flat hf], hl.length⟩
  · simp at ha
  · exact hr

/-- **Peeling a value prefix.** -/
theorem LRel.peel : ∀ (vs : List Val) {X R : List Admin}, LRel (vals vs ++ X) R →
    ∃ R₀, R = vals vs ++ R₀ ∧ LRel X R₀
  | [], _, _, h => ⟨_, rfl, h⟩
  | v :: vs, X, R, h => by
    rcases (show LRel (v.toAdmin :: (vals vs ++ X)) R by simpa [Sim.vals_cons'] using h).cons_inv with
      ⟨b, r, rfl, hab, hl⟩ | ⟨x, t, l, r, hx, -⟩ | ⟨hk, -⟩
    · obtain ⟨R₀, rfl, h₀⟩ := LRel.peel vs hl
      exact ⟨R₀, by rw [hab.eq_of_flat (flat_toAdmin v)]; simp, h₀⟩
    · exact absurd hx (toAdmin_ne_localGet v x)
    · rcases hk with hk | hk
      · exact absurd hk (toAdmin_ne_trap v).1
      · exact absurd hk (toAdmin_ne_trap v).2

/-- Values are related only to themselves. -/
theorem LRel.eq_vals {vs : List Val} {R : List Admin} (h : LRel (vals vs) R) : R = vals vs := by
  obtain ⟨R₀, rfl, h₀⟩ := LRel.peel vs (X := []) (by simpa using h)
  cases h₀
  simp

/-- **An exit shape** `val* k rest` with `k` flat and not `local.get`: the right side is
`val* k rest'`. -/
theorem LRel.exit_inv {vs : List Val} {k : Admin} {rest R : List Admin}
    (h : LRel (vals vs ++ k :: rest) R) (hk : Flat k) (hl : ∀ x, k ≠ .plain (.localGet x)) :
    ∃ R', R = vals vs ++ k :: R' := by
  obtain ⟨R₀, rfl, h₀⟩ := LRel.peel vs h
  rcases h₀.cons_inv with ⟨b, r, rfl, hab, -⟩ | ⟨x, -, -, -, hx, -⟩ | ⟨-, r, rfl, -⟩
  · exact ⟨r, by rw [hab.eq_of_flat hk]⟩
  · exact absurd hx (hl x)
  · exact ⟨r, rfl⟩

/-- A `trap` is related only to itself. -/
theorem LRel.eq_trap {R : List Admin} (h : LRel [.trap] R) : R = [.trap] := by
  obtain ⟨r, rfl, hr⟩ := h.kernel_inv (Or.inl rfl)
  cases r with
  | nil => rfl
  | cons => simp at hr

/-- A thrown exception is related only to itself. -/
theorem LRel.eq_throwing {a : Nat} {R : List Admin} (h : LRel (throwing a) R) :
    R = throwing a := by
  have h' : LRel (vals [.ref (.exn a)] ++ [.plain .throwRef]) R := by
    simpa [vals, throwing, Val.toAdmin] using h
  obtain ⟨R₀, rfl, h₀⟩ := LRel.peel _ h'
  obtain ⟨r, rfl, hr⟩ := h₀.kernel_inv (Or.inr rfl)
  cases r with
  | nil => simp [vals, throwing, Val.toAdmin]
  | cons => simp at hr

/-- **Results are related only to themselves.** -/
theorem LRel.result_inv {r : Result} {R : List Admin} (h : LRel r.toAdmin R) : R = r.toAdmin := by
  cases r with
  | values vs => exact h.eq_vals
  | throw a => exact h.eq_throwing
  | trap => exact h.eq_trap

/-- A related `LABEL`. -/
theorem ARel.label_inv {n : Nat} {c : List Instr} {b : List Admin} {a' : Admin}
    (h : ARel (.label n c b) a') :
    ∃ c' b', a' = .label n c' b' ∧ InstrsRel fuseBI c c' ∧ LRel b b' := by
  cases h with
  | refl => exact ⟨c, b, rfl, InstrsRel.refl _, LRel.refl _⟩
  | label _ hc hb => exact ⟨_, _, rfl, hc, hb⟩

/-- A related `HANDLER`. -/
theorem ARel.handler_inv {n : Nat} {cs : List Catch} {b : List Admin} {a' : Admin}
    (h : ARel (.handler n cs b) a') : ∃ b', a' = .handler n cs b' ∧ LRel b b' := by
  cases h with
  | refl => exact ⟨b, rfl, LRel.refl _⟩
  | handler _ _ hb => exact ⟨_, rfl, hb⟩

/-- A related `FRAME`. -/
theorem ARel.frame_inv {n : Nat} {fi : Frame} {b : List Admin} {a' : Admin}
    (h : ARel (.frame n fi b) a') : ∃ b', a' = .frame n fi b' ∧ LRel b b' := by
  cases h with
  | refl => exact ⟨b, rfl, LRel.refl _⟩
  | frame _ _ hb => exact ⟨_, rfl, hb⟩

end Silmaril.Proofs.Wasm.Wasmi
