module

public import Silmaril.Proofs.Wasm.Wasmi.LooseW.Fuse
public import Silmaril.Wasm.Execution.Core.Sim.Context

@[expose] public section

/-!
# The simulation relation from `fuseW`'s translated code to the loose model `LooseW`

As `Silmaril.Proofs.Wasm.Wasmi.SimRel` for `fuse`, with two changes:

* `group g x t`: the translation `g.tgt x t` of any of the five shapes against its source
  `g.src x t`. When the left reads the local, the right takes `selectEitherW` at shape `g` with
  the constant the translation reads;
* `cut`: a `trap` or `THROW_REF` followed by code that is empty on one side exactly when it is
  empty on the other. The `eqz` shape has three source instructions against four translated
  ones, so lengths are no longer preserved; the simulation stutters instead
  (`Silmaril.Proofs.Wasm.Wasmi.LooseW.Sim`).

New proofs.
-/

namespace Silmaril.Proofs.Wasm.Wasmi.LooseW

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.Wasmi Silmaril.Wasm.Wasmi.LooseW

mutual
/-- Related administrative instructions (left: translated, right: source). -/
inductive ARel : Admin → Admin → Prop where
  | refl (a : Admin) : ARel a a
  | plain {i j : Instr} : InstrRel fuseWBI i j → ARel (.plain i) (.plain j)
  | label (n : Nat) {c c' : List Instr} {b b' : List Admin} :
      InstrsRel fuseWBI c c' → LRel b b' → ARel (.label n c b) (.label n c' b')
  | handler (n : Nat) (cs : List Catch) {b b' : List Admin} :
      LRel b b' → ARel (.handler n cs b) (.handler n cs b')
  | frame (n : Nat) (fi : Frame) {b b' : List Admin} :
      LRel b b' → ARel (.frame n fi b) (.frame n fi b')

/-- Related runtime code (left: translated, right: source). -/
inductive LRel : List Admin → List Admin → Prop where
  | nil : LRel [] []
  | cons {a b : Admin} {l r : List Admin} : ARel a b → LRel l r → LRel (a :: l) (b :: r)
  | group (g : FuseShape) (x : LocalIdx) (t : Option (List ValType)) {l r : List Admin} :
      LRel l r → LRel (expression (g.tgt x t) ++ l) (expression (g.src x t) ++ r)
  | cut {k : Admin} (hk : k = .trap ∨ k = .plain .throwRef) {l r : List Admin} :
      (l = [] ↔ r = []) → LRel (k :: l) (k :: r)
end

/-! ## Structure -/

theorem src_ne_nil (g : FuseShape) (x : LocalIdx) (t : Option (List ValType)) :
    expression (g.src x t) ≠ [] := by
  cases g <;> simp [expression, FuseShape.src]

/-- **Related codes are empty together.** -/
theorem LRel.nil_iff : ∀ {l r : List Admin}, LRel l r → (l = [] ↔ r = [])
  | _, _, .nil => Iff.rfl
  | _, _, .cons _ _ => by simp
  | _, _, .group g x t _ => by
    simp only [List.append_eq_nil_iff, src_ne_nil, false_and, iff_false]
    simp [expression, FuseShape.tgt]
  | _, _, .cut _ _ => by simp

theorem LRel.refl : ∀ l : List Admin, LRel l l
  | [] => .nil
  | a :: l => .cons (.refl a) (LRel.refl l)

theorem LRel.append : ∀ {a b c d : List Admin}, LRel a b → LRel c d → LRel (a ++ c) (b ++ d)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h₁ h₂, h => .cons h₁ (h₂.append h)
  | _, _, _, _, .group g x t h₁, h => by
    rw [List.append_assoc, List.append_assoc]; exact .group g x t (h₁.append h)
  | _, _, _, _, .cut hk h₁, h => .cut hk (by simp only [List.append_eq, List.append_eq_nil_iff, h₁, h.nil_iff])

theorem LRel.vals_append (vs : List Val) {l r : List Admin} (h : LRel l r) :
    LRel (vals vs ++ l) (vals vs ++ r) :=
  (LRel.refl _).append h

/-- Lowering related source sequences. -/
theorem LRel.src : ∀ {x y : List Instr}, InstrsRel fuseWBI x y →
    LRel (expression x) (expression y)
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (.plain h) (LRel.src t)
  | _, _, .base ⟨g, x, t, h₁, h₂⟩ => by
    subst h₁ h₂; simpa using LRel.group g x t .nil
  | _, _, .append h₁ h₂ => by
    simp only [expression, List.map_append]; exact (LRel.src h₁).append (LRel.src h₂)

mutual
/-- silmaril-lean's closure without base pairs is contained in `ARel`. -/
theorem ARel.ofAdminRel : ∀ {a b : Admin}, AdminRel fuseWBI (fun _ _ => False) a b → ARel a b
  | _, _, .refl a => .refl a
  | _, _, .plain h => .plain h
  | _, _, .label n hc hb => .label n hc (LRel.ofAdminsRel hb)
  | _, _, .handler n cs hb => .handler n cs (LRel.ofAdminsRel hb)
  | _, _, .frame n f hb => .frame n f (LRel.ofAdminsRel hb)

/-- silmaril-lean's closure without base pairs is contained in `LRel`. -/
theorem LRel.ofAdminsRel : ∀ {x y : List Admin},
    AdminsRel fuseWBI (fun _ _ => False) x y → LRel x y
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
    (∃ (g : FuseShape) (x : LocalIdx) (t : Option (List ValType)) (l r : List Admin),
      a = .plain (.localGet x) ∧
      es = [.plain .drop, .plain (.intConst .i32 g.cond), .plain (.select t)] ++ l ∧
      R = expression (g.src x t) ++ r ∧ LRel l r) ∨
    ((a = .trap ∨ a = .plain .throwRef) ∧ ∃ r, R = a :: r ∧ (es = [] ↔ r = [])) := by
  generalize hw : a :: es = w at h
  cases h with
  | nil => cases hw
  | cons hab hl =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hw
    exact Or.inl ⟨_, _, rfl, hab, hl⟩
  | group g x t hl =>
    simp only [expression, FuseShape.tgt, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.cons.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact Or.inr (Or.inl ⟨g, x, t, _, _, rfl, rfl, rfl, hl⟩)
  | cut hk hl =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hw
    exact Or.inr (Or.inr ⟨hk, _, rfl, hl⟩)

/-- At a `trap` or `THROW_REF` head, the right side has the same head and a tail that is
empty exactly when the left one is. -/
theorem LRel.kernel_inv {a : Admin} {es R : List Admin} (h : LRel (a :: es) R)
    (ha : a = .trap ∨ a = .plain .throwRef) : ∃ r, R = a :: r ∧ (es = [] ↔ r = []) := by
  rcases h.cons_inv with ⟨b, r, rfl, hab, hl⟩ | ⟨g, x, t, l, r, rfl, -⟩ | ⟨-, hr⟩
  · have hf : Flat a := by rcases ha with rfl | rfl <;> trivial
    exact ⟨r, by rw [hab.eq_of_flat hf], hl.nil_iff⟩
  · simp at ha
  · exact hr

/-- **Peeling a value prefix.** -/
theorem LRel.peel : ∀ (vs : List Val) {X R : List Admin}, LRel (vals vs ++ X) R →
    ∃ R₀, R = vals vs ++ R₀ ∧ LRel X R₀
  | [], _, _, h => ⟨_, rfl, h⟩
  | v :: vs, X, R, h => by
    rcases (show LRel (v.toAdmin :: (vals vs ++ X)) R by simpa [Sim.vals_cons'] using h).cons_inv with
      ⟨b, r, rfl, hab, hl⟩ | ⟨g, x, t, l, r, hx, -⟩ | ⟨hk, -⟩
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
  rcases h₀.cons_inv with ⟨b, r, rfl, hab, -⟩ | ⟨-, x, -, -, -, hx, -⟩ | ⟨-, r, rfl, -⟩
  · exact ⟨r, by rw [hab.eq_of_flat hk]⟩
  · exact absurd hx (hl x)
  · exact ⟨r, rfl⟩

/-- A `trap` is related only to itself. -/
theorem LRel.eq_trap {R : List Admin} (h : LRel [.trap] R) : R = [.trap] := by
  obtain ⟨r, rfl, hr⟩ := h.kernel_inv (Or.inl rfl)
  rw [hr.mp rfl]

/-- A thrown exception is related only to itself. -/
theorem LRel.eq_throwing {a : Nat} {R : List Admin} (h : LRel (throwing a) R) :
    R = throwing a := by
  have h' : LRel (vals [.ref (.exn a)] ++ [.plain .throwRef]) R := by
    simpa [vals, throwing, Val.toAdmin] using h
  obtain ⟨R₀, rfl, h₀⟩ := LRel.peel _ h'
  obtain ⟨r, rfl, hr⟩ := h₀.kernel_inv (Or.inr rfl)
  rw [hr.mp rfl]; simp [vals, throwing, Val.toAdmin]

/-- **Results are related only to themselves.** -/
theorem LRel.result_inv {r : Result} {R : List Admin} (h : LRel r.toAdmin R) : R = r.toAdmin := by
  cases r with
  | values vs => exact h.eq_vals
  | throw a => exact h.eq_throwing
  | trap => exact h.eq_trap

/-- A related `LABEL`. -/
theorem ARel.label_inv {n : Nat} {c : List Instr} {b : List Admin} {a' : Admin}
    (h : ARel (.label n c b) a') :
    ∃ c' b', a' = .label n c' b' ∧ InstrsRel fuseWBI c c' ∧ LRel b b' := by
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

end Silmaril.Proofs.Wasm.Wasmi.LooseW
