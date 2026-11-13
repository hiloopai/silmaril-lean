module

public import Silmaril.Wasm.Resource.Protocol.Defs
public import Silmaril.Wasm.Spec.Format.Thms

/-!
# Resource protocols: runs, acceptance and the protocol logic

Runs compose along concatenation (`run_append`); acceptance is prefix-closed
(`Accepts.of_prefix`) and decided by `acceptsB` (`acceptsB_iff`); `comap` and `prod` act on runs
as expected (`accepts_comap`, `accepts_prod_iff`); a protocol is the action predicate "the
extended history is accepted" (`everyPos_iff`); and satisfaction in the protocol logic is
acceptance of every trace (`models_protoLogic_iff`), so a single rejected trace refutes it
(`not_models_of_trace`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm.Spec

namespace Protocol

variable {S S' E E' : Type} (p : Protocol S E)

@[simp] theorem run_nil (q : S) : p.run q [] = some q := rfl

@[simp] theorem run_cons (q : S) (e : E) (t : List E) :
    p.run q (e :: t) = (p.step q e).bind fun q' => p.run q' t := rfl

/-- Runs compose along concatenation. -/
theorem run_append (q : S) (t u : List E) :
    p.run q (t ++ u) = (p.run q t).bind fun q' => p.run q' u := by
  induction t generalizing q with
  | nil => rfl
  | cons e t ih =>
    simp only [List.cons_append, run_cons]
    cases p.step q e <;> simp [ih]

theorem run_concat (q : S) (t : List E) (e : E) :
    p.run q (t ++ [e]) = (p.run q t).bind fun q' => p.step q' e := by
  rw [run_append]
  cases p.run q t <;> simp

theorem accepts_nil : p.Accepts [] := rfl

theorem acceptsB_iff (t : List E) : p.acceptsB t = true ↔ p.Accepts t := Iff.rfl

theorem accepts_iff_exists (t : List E) : p.Accepts t ↔ ∃ q, p.run p.init t = some q :=
  Option.isSome_iff_exists

/-- Acceptance is closed under prefixes. -/
theorem Accepts.of_prefix {p : Protocol S E} {s t : List E} (ht : p.Accepts t) (hs : s <+: t) : p.Accepts s := by
  obtain ⟨u, rfl⟩ := hs
  rw [accepts_iff_exists] at ht ⊢
  obtain ⟨q, hq⟩ := ht
  rw [run_append] at hq
  cases h : p.run p.init s with
  | none => rw [h] at hq; cases hq
  | some q' => exact ⟨q', rfl⟩

/-- One more event is accepted iff the reached state can step on it. -/
theorem accepts_concat_iff (t : List E) (e : E) :
    p.Accepts (t ++ [e]) ↔ ∃ q, p.run p.init t = some q ∧ ∃ q', p.step q e = some q' := by
  rw [accepts_iff_exists, run_concat]
  constructor
  · rintro ⟨q', hq'⟩
    cases h : p.run p.init t with
    | none => rw [h] at hq'; cases hq'
    | some q => rw [h] at hq'; exact ⟨q, rfl, q', hq'⟩
  · rintro ⟨q, hq, q', hq'⟩
    exact ⟨q', by rw [hq]; exact hq'⟩

/-- A rejected word stays rejected under extension. -/
theorem not_accepts_append {t : List E} (ht : ¬ p.Accepts t) (u : List E) :
    ¬ p.Accepts (t ++ u) := fun h => ht (Accepts.of_prefix h (List.prefix_append t u))

theorem run_comap (g : E' → E) (q : S) (t : List E') :
    (p.comap g).run q t = p.run q (t.map g) := by
  induction t generalizing q with
  | nil => rfl
  | cons e t ih =>
    rw [List.map_cons, run_cons, run_cons]
    change (p.step q (g e)).bind _ = _
    cases p.step q (g e) with
    | none => rfl
    | some q' => exact ih q'

theorem accepts_comap (g : E' → E) (t : List E') :
    (p.comap g).Accepts t ↔ p.Accepts (t.map g) := by
  unfold Accepts
  rw [run_comap]
  rfl

theorem run_prod (p' : Protocol S' E) (q : S) (q' : S') (t : List E) :
    (p.prod p').run (q, q') t =
      (p.run q t).bind fun a => (p'.run q' t).map fun b => (a, b) := by
  induction t generalizing q q' with
  | nil => rfl
  | cons e t ih =>
    rw [run_cons, run_cons, run_cons]
    change ((p.step q e).bind fun a => (p'.step q' e).map fun b => (a, b)).bind _ = _
    cases p.step q e with
    | none => rfl
    | some a =>
      cases p'.step q' e with
      | none => simp
      | some b => simp [ih]

/-- The product accepts exactly the words both protocols accept. -/
theorem accepts_prod_iff (p' : Protocol S' E) (t : List E) :
    (p.prod p').Accepts t ↔ p.Accepts t ∧ p'.Accepts t := by
  unfold Accepts
  have : (p.prod p').init = (p.init, p'.init) := rfl
  rw [this, run_prod]
  cases p.run p.init t <;> cases p'.run p'.init t <;> simp

/-- **A protocol is an action invariant**: every position satisfies `toActPred` iff the word is
accepted. -/
theorem everyPos_iff (t : List E) : EveryPos p.toActPred t ↔ p.Accepts t := by
  constructor
  · intro h
    rcases List.eq_nil_or_concat t with rfl | ⟨h', e, rfl⟩
    · exact p.accepts_nil
    · have := h h' e [] (by simp)
      simpa [toActPred] using this
  · intro h h' e r hr
    exact Accepts.of_prefix h ⟨r, by simp [hr]⟩

end Protocol

variable {Ty A R S : Type}

/-- **Satisfaction in the protocol logic** is acceptance of every trace. -/
theorem models_protoLogic_iff (Sem : Semantics Ty A R) {X : Iface Ty} (p : Sem.Prog X)
    (φ : Protocol S (Event A R X)) :
    Models (protoLogic Ty A R S) Sem p φ ↔ ∀ t ∈ Sem.traces p, φ.Accepts t :=
  models_iff _ _ _ _

/-- **Refutation by one trace**: a trace of the program that the protocol rejects. -/
theorem not_models_of_trace (Sem : Semantics Ty A R) {X : Iface Ty} (p : Sem.Prog X)
    (φ : Protocol S (Event A R X)) {t : List (Event A R X)} (ht : t ∈ Sem.traces p)
    (hrej : φ.acceptsB t = false) : ¬ Models (protoLogic Ty A R S) Sem p φ := by
  rw [models_protoLogic_iff]
  intro h
  have := h t ht
  rw [← Protocol.acceptsB_iff, hrej] at this
  cases this

/-- **Protocols are action invariants**: the logic map from protocols into `act`. -/
def Protocol.toActMap : LogicMap (protoLogic Ty A R S) (act Ty A R) :=
  LogicMap.ofTrace (fun φ => Protocol.toAct φ) fun φ t => φ.everyPos_iff t

/-- Models of a product protocol are models of both. -/
theorem models_prod_iff (Sem : Semantics Ty A R) {S' : Type} {X : Iface Ty} (p : Sem.Prog X)
    (φ : Protocol S (Event A R X)) (ψ : Protocol S' (Event A R X)) :
    Models (protoLogic Ty A R (S × S')) Sem p (φ.prod ψ) ↔
      Models (protoLogic Ty A R S) Sem p φ ∧ Models (protoLogic Ty A R S') Sem p ψ := by
  simp only [models_protoLogic_iff, Protocol.accepts_prod_iff]
  exact ⟨fun h => ⟨fun t ht => (h t ht).1, fun t ht => (h t ht).2⟩,
    fun h t ht => ⟨h.1 t ht, h.2 t ht⟩⟩

end Silmaril.Wasm.Resource
