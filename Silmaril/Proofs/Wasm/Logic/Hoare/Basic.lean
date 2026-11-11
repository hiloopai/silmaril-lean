module

public import Silmaril.Wasm.Logic.Hoare.Defs
public import Silmaril.Wasm.SingleThreaded.InertHead
public import Silmaril.Wasm.SingleThreaded.Exec.Driver
public import Silmaril.Wasm.Execution.Core.Sim.RankedSegments

/-!
# The every-run logic: safety, exits and irreducible codes

* index and postcondition monotonicity of `Safe`, and the introduction forms
  `Safe.of_exits`, `Safe.of_step`;
* the codes that do not step under **any** host (values, `trap`, a bare thrown
  exception, and codes whose first non-value is `br`, `return` or
  `return_call_ref`), from silmaril-lean's host-free stuckness lemmas
  (`Silmaril.Wasm.SingleThreaded.Det.not_step_*`) and its host-call
  decomposition `Silmaril.Wasm.SingleThreaded.Step.split_host`;
* the outcome of an exit is determined by its code (`exits_*_inv`);
* a trap or an exception that is still inside a sequence only discards values
  and dead code (`Exits.step`, from `Sim.Step.exitShape_cut_rank`).

All of this is new (a Silmaril addition); it uses silmaril-lean's lemmas as cited.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Hoare

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded (decompose? decompHead_plain decompHead_trap
  decompHead_returnCallRef decompose?_vals_cons_none)
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Unfolding -/

@[simp] theorem safe_zero (Q : Post H) (c : Config H) : Safe P host Q 0 c := trivial

theorem safe_succ (Q : Post H) (n : Nat) (c : Config H) :
    Safe P host Q (n + 1) c ↔ ((∃ o, Exits o c.code ∧ Q c.store c.frame o) ∨
      ((∃ c', Step P host c c') ∧ ∀ c', Step P host c c' → Safe P host Q n c')) := Iff.rfl

/-- An exit satisfying the postcondition is safe. -/
theorem Safe.of_exits {Q : Post H} {n : Nat} {c : Config H} {o : Outcome} (he : Exits o c.code)
    (hq : Q c.store c.frame o) : Safe P host Q n c := by
  cases n with
  | zero => trivial
  | succ n => exact Or.inl ⟨o, he, hq⟩

/-- A code that can step, with every successor safe, is safe for one more step. -/
theorem Safe.of_step {Q : Post H} {n : Nat} {c : Config H} (hp : ∃ c', Step P host c c')
    (hs : ∀ c', Step P host c c' → Safe P host Q n c') : Safe P host Q (n + 1) c :=
  Or.inr ⟨hp, hs⟩

/-- Fewer steps. -/
theorem Safe.mono : ∀ {n m : Nat} {Q : Post H} {c : Config H}, m ≤ n →
    Safe P host Q n c → Safe P host Q m c
  | _, 0, _, _, _, _ => trivial
  | 0, _ + 1, _, _, hmn, _ => absurd hmn (by omega)
  | _ + 1, _ + 1, _, _, hmn, h =>
    h.imp id fun ⟨hp, hs⟩ => ⟨hp, fun c' hc => Safe.mono (by omega) (hs c' hc)⟩

/-- A weaker postcondition. -/
theorem Safe.post_mono : ∀ {n : Nat} {Q Q' : Post H} {c : Config H},
    (∀ s f o, Q s f o → Q' s f o) → Safe P host Q n c → Safe P host Q' n c
  | 0, _, _, _, _, _ => trivial
  | _ + 1, _, _, _, hq, h =>
    h.imp (fun ⟨o, he, h⟩ => ⟨o, he, hq _ _ _ h⟩)
      fun ⟨hp, hs⟩ => ⟨hp, fun c' hc => Safe.post_mono hq (hs c' hc)⟩

theorem HWP.mono {s : Store H} {f : Frame} {code : List Admin} {Q Q' : Post H}
    (hq : ∀ s f o, Q s f o → Q' s f o) (h : HWP P host s f code Q) : HWP P host s f code Q' :=
  fun n => (h n).post_mono hq

theorem HWP.of_exits {s : Store H} {f : Frame} {code : List Admin} {Q : Post H} {o : Outcome}
    (he : Exits o code) (hq : Q s f o) : HWP P host s f code Q :=
  fun _ => Safe.of_exits (c := ⟨s, f, code⟩) he hq

/-- Values are a normal exit. -/
theorem HWP.of_vals {s : Store H} {f : Frame} {vs : List Val} {Q : Post H}
    (hq : Q s f (.normal vs)) : HWP P host s f (vals vs) Q :=
  HWP.of_exits (o := .normal vs) rfl hq

theorem seqPost.toK {c₂ : List Admin} {Q : Post H} (k : Nat) {s : Store H} {f : Frame}
    {o : Outcome} (h : seqPost P host c₂ Q s f o) : seqPostK P host c₂ Q k s f o := by
  cases o with
  | normal vs => exact (h : HWP P host s f _ Q) k
  | _ => exact h

theorem labelPost.toK {n : Nat} {cont : List Instr} {us : List Val} {Q : Post H} (k : Nat)
    {s : Store H} {f : Frame} {o : Outcome} (h : labelPost P host n cont us Q s f o) :
    labelPostK P host n cont us Q k s f o := by
  rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | a | ⟨vs, a, c⟩
  · exact h
  · obtain ⟨vs₁, vs₂, he, hn, hw⟩ := h
    exact ⟨vs₁, vs₂, he, hn, hw k⟩
  all_goals exact h

/-! ## Codes that do not step -/

/-- A configuration without a host-call redex steps only by host-free rules. -/
theorem step_noHost {c c' : Config H} (hd : decompose? c.store c.code = none)
    (h : Step P host c c') : Step P SingleThreaded.Det.noHost c c' := by
  rcases SingleThreaded.Step.split_host h with h | ⟨E, a, hh, args, hd', -⟩
  · exact h
  · rw [hd] at hd'
    cases hd'

theorem not_step_vals {s : Store H} {f : Frame} {vs : List Val} {c' : Config H} :
    ¬ Step P host ⟨s, f, vals vs⟩ c' :=
  Core.Step.not_vals

theorem not_step_trap {s : Store H} {f : Frame} {c' : Config H} :
    ¬ Step P host ⟨s, f, [.trap]⟩ c' := fun h =>
  SingleThreaded.Det.not_step_trap
    (step_noHost (decompose?_vals_cons_none (vs := []) (r := []) rfl
      fun _ _ => decompHead_trap) h)

theorem not_step_throwing {s : Store H} {f : Frame} {a : Nat} {c' : Config H} :
    ¬ Step P host ⟨s, f, throwing a⟩ c' := fun h =>
  SingleThreaded.Det.not_step_throwing
    (step_noHost (decompose?_vals_cons_none (vs := [.ref (.exn a)]) (r := []) rfl
      fun _ _ => decompHead_plain rfl) h)

/-- The heads that only reduce through an enclosing label, handler or frame. -/
theorem blocked_noRedex {s : Store H} {e : Admin} (he : SingleThreaded.Det.Blocked e)
    (vs : List Val) (rest : List Admin) : SingleThreaded.decompHead s vs e rest = none := by
  rcases he with ⟨l, rfl⟩ | rfl | hc
  · exact decompHead_plain rfl
  · exact decompHead_plain rfl
  · exact decompHead_returnCallRef hc

theorem blocked_val_none {e : Admin} (he : SingleThreaded.Det.Blocked e) : e.val? = none := by
  rcases he with ⟨l, rfl⟩ | rfl | hc
  · rfl
  · rfl
  · exact SingleThreaded.val?_returnCallRef hc

theorem not_step_blocked {s : Store H} {f : Frame} {vs : List Val} {e : Admin}
    {rest : List Admin} {c' : Config H} (he : SingleThreaded.Det.Blocked e) :
    ¬ Step P host ⟨s, f, vals vs ++ e :: rest⟩ c' := fun h => by
  have hd : decompose? s (vals vs ++ e :: rest) = none :=
    decompose?_vals_cons_none (blocked_val_none he) (blocked_noRedex he)
  have hf : SingleThreaded.Det.fnv (vals vs ++ e :: rest) = (vs, e :: rest) := by
    simp [SingleThreaded.Det.fnv_cons_of_none (blocked_val_none he)]
  exact SingleThreaded.Det.not_step_blocked (step_noHost hd h) hf he

/-! ## The outcome of an exit is determined by its code -/


/-- The first-non-value split of an exit of outcome `o`. -/
def FnvOk : Outcome → List Val × List Admin → Prop
  | .normal vs, p => p = (vs, [])
  | .br l vs, p => ∃ (x : LabelIdx) (rest : List Admin), x.toNat = l ∧
      p = (vs, .plain (.br x) :: rest)
  | .ret vs, p => ∃ rest : List Admin, p = (vs, .plain .return_ :: rest)
  | .trap, p => ∃ (vs : List Val) (rest : List Admin), p = (vs, .trap :: rest)
  | .throw a, p => ∃ (vs : List Val) (rest : List Admin),
      p = (vs ++ [.ref (.exn a)], .plain .throwRef :: rest)
  | .tail vs a r, p => ((∃ y, r = .plain (.returnCallRef y)) ∨ (∃ d, r = .returnCallRefType d)) ∧
      ∃ rest : List Admin, p = (vs ++ [.ref (.func a)], r :: rest)

theorem fnv_vals_cons {vs : List Val} {e : Admin} {rest : List Admin} (he : e.val? = none) :
    SingleThreaded.Det.fnv (vals vs ++ e :: rest) = (vs, e :: rest) := by
  simp [SingleThreaded.Det.fnv_cons_of_none he]

/-- The code of a thrown exception, split at its first non-value. -/
theorem throwing_code (vs : List Val) (a : Nat) (rest : List Admin) :
    vals vs ++ throwing a ++ rest = vals (vs ++ [.ref (.exn a)]) ++ .plain .throwRef :: rest := by
  simp [vals, Val.toAdmin]

/-- The code of a tail call, split at its first non-value. -/
theorem tail_code (vs : List Val) (a : Nat) (r : Admin) (rest : List Admin) :
    vals vs ++ .ref (.func a) :: r :: rest = vals (vs ++ [.ref (.func a)]) ++ r :: rest := by
  simp [vals, Val.toAdmin]

theorem fnv_tail_code {vs : List Val} {a : Nat} {r : Admin} {rest : List Admin}
    (hr : r.IsReturnCallRef) :
    SingleThreaded.Det.fnv (vals vs ++ .ref (.func a) :: r :: rest) =
      (vs ++ [.ref (.func a)], r :: rest) := by
  rw [tail_code]
  exact fnv_vals_cons (SingleThreaded.val?_returnCallRef hr)

theorem Exits.fnv {o : Outcome} {c : List Admin} (h : Exits o c) :
    FnvOk o (SingleThreaded.Det.fnv c) := by
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩
  · rw [show c = vals vs from h, SingleThreaded.Det.fnv_vals]; rfl
  · obtain ⟨x, rest, hx, rfl⟩ := h
    exact ⟨x, rest, hx, fnv_vals_cons rfl⟩
  · obtain ⟨rest, rfl⟩ := h
    exact ⟨rest, fnv_vals_cons rfl⟩
  · obtain ⟨vs, rest, rfl⟩ := h
    exact ⟨vs, rest, fnv_vals_cons rfl⟩
  · obtain ⟨vs, rest, rfl⟩ := h
    exact ⟨vs, rest, (throwing_code vs a rest).symm ▸ fnv_vals_cons rfl⟩
  · obtain ⟨hr, rest, rfl⟩ := h
    exact ⟨SingleThreaded.Det.IsReturnCallRef.cases hr, rest, fnv_tail_code hr⟩

/-- A head that is not a `return_call_ref` is not a tail call. -/
theorem fnvOk_tail_ne {vs W : List Val} {a : Nat} {r e : Admin} {rest : List Admin}
    (he : ∀ y, e ≠ .plain (.returnCallRef y)) (hd : ∀ d, e ≠ .returnCallRefType d) :
    ¬ FnvOk (.tail vs a r) (W, e :: rest) := by
  rintro ⟨hr, rest', h⟩
  have hre : e = r := (List.cons.inj (Prod.mk.inj h).2).1
  rcases hr with ⟨y, rfl⟩ | ⟨d, rfl⟩
  · exact he y hre
  · exact hd d hre

theorem exits_vals_inv {o : Outcome} {vs : List Val} (h : Exits o (vals vs)) :
    o = .normal vs := by
  have h' : FnvOk o (vs, []) := by simpa using h.fnv
  cases o <;> simp_all [FnvOk]

theorem exits_trap_inv {o : Outcome} {vs : List Val} {rest : List Admin}
    (h : Exits o (vals vs ++ .trap :: rest)) : o = .trap := by
  have h' : FnvOk o (vs, .trap :: rest) := by simpa [fnv_vals_cons (e := .trap) rfl] using h.fnv
  cases o
  all_goals first
    | exact absurd h' (fnvOk_tail_ne (by simp) (by simp))
    | simp_all [FnvOk]

theorem exits_throw_inv {o : Outcome} {vs : List Val} {a : Nat} {rest : List Admin}
    (h : Exits o (vals vs ++ throwing a ++ rest)) : o = .throw a := by
  have h' : FnvOk o (vs ++ [.ref (.exn a)], .plain .throwRef :: rest) := by
    rw [← fnv_vals_cons (e := .plain .throwRef) rfl, ← throwing_code]; exact h.fnv
  cases o
  all_goals first
    | exact absurd h' (fnvOk_tail_ne (by simp) (by simp))
    | simp_all [FnvOk]

theorem exits_br_inv {o : Outcome} {vs : List Val} {x : LabelIdx} {rest : List Admin}
    (h : Exits o (vals vs ++ .plain (.br x) :: rest)) : o = .br x.toNat vs := by
  have h' : FnvOk o (vs, .plain (.br x) :: rest) := by simpa [fnv_vals_cons (e := .plain (.br x)) rfl] using h.fnv
  cases o
  all_goals first
    | exact absurd h' (fnvOk_tail_ne (by simp) (by simp))
    | simp_all [FnvOk]

theorem exits_ret_inv {o : Outcome} {vs : List Val} {rest : List Admin}
    (h : Exits o (vals vs ++ .plain .return_ :: rest)) : o = .ret vs := by
  have h' : FnvOk o (vs, .plain .return_ :: rest) := by
    simpa [fnv_vals_cons (e := .plain .return_) rfl] using h.fnv
  cases o
  all_goals first
    | exact absurd h' (fnvOk_tail_ne (by simp) (by simp))
    | simp_all [FnvOk]

theorem exits_tail_inv {o : Outcome} {vs : List Val} {a : Nat} {r : Admin} {rest : List Admin}
    (hr : r.IsReturnCallRef) (h : Exits o (vals vs ++ .ref (.func a) :: r :: rest)) :
    o = .tail vs a r := by
  have h' : FnvOk o (vs ++ [.ref (.func a)], r :: rest) := by
    rw [← fnv_tail_code hr]; exact h.fnv
  rcases SingleThreaded.Det.IsReturnCallRef.cases hr with ⟨y, rfl⟩ | ⟨d, rfl⟩ <;>
    cases o <;> simp_all [FnvOk]

/-! ## Exits under sequencing -/

/-- Every exit other than falling through ignores what follows. -/
theorem Exits.append {o : Outcome} {c : List Admin} (he : Exits o c)
    (hn : ∀ vs, o ≠ .normal vs) (d : List Admin) : Exits o (c ++ d) := by
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩
  · exact (hn vs rfl).elim
  · obtain ⟨x, rest, hx, rfl⟩ := he
    exact ⟨x, rest ++ d, hx, by simp⟩
  · obtain ⟨rest, rfl⟩ := he
    exact ⟨rest ++ d, by simp⟩
  · obtain ⟨vs, rest, rfl⟩ := he
    exact ⟨vs, rest ++ d, by simp⟩
  · obtain ⟨vs, rest, rfl⟩ := he
    exact ⟨vs, rest ++ d, by simp⟩
  · obtain ⟨hr, rest, rfl⟩ := he
    exact ⟨hr, rest ++ d, by simp⟩

/-- A trap inside a sequence steps only by discarding values and dead code. -/
theorem exits_trap_step {s s' : Store H} {f f' : Frame} {vs : List Val} {rest c' : List Admin}
    (h : Step P host ⟨s, f, vals vs ++ .trap :: rest⟩ ⟨s', f', c'⟩) :
    s' = s ∧ f' = f ∧ Exits .trap c' ∧ Sim.codeSize c' < Sim.codeSize (vals vs ++ .trap :: rest) := by
  have h' : Step P host ⟨s, f, vals vs ++ [.trap] ++ rest⟩ ⟨s', f', c'⟩ := by simpa using h
  obtain ⟨hs, hf, ⟨U, X, rfl⟩, hr⟩ :=
    Sim.Step.exitShape_cut_rank (rank := Sim.codeSize) (Or.inl rfl) h'
  exact ⟨hs, hf, ⟨U, X, by simp⟩, by simpa using hr⟩

/-- An exception inside a sequence steps only by discarding values and dead code. -/
theorem exits_throw_step {s s' : Store H} {f f' : Frame} {vs : List Val} {a : Nat}
    {rest c' : List Admin} (h : Step P host ⟨s, f, vals vs ++ throwing a ++ rest⟩ ⟨s', f', c'⟩) :
    s' = s ∧ f' = f ∧ Exits (.throw a) c' ∧
      Sim.codeSize c' < Sim.codeSize (vals vs ++ throwing a ++ rest) := by
  obtain ⟨hs, hf, ⟨U, X, rfl⟩, hr⟩ :=
    Sim.Step.exitShape_cut_rank (rank := Sim.codeSize) (Or.inr ⟨a, rfl⟩) h
  exact ⟨hs, hf, ⟨U, X, rfl⟩, hr⟩

/-- Exits that can still step: a trap or an exception with values before it or
dead code after it. Such a step keeps the store, the frame and the outcome, and
shortens the code. -/
theorem Exits.step {o : Outcome} {s s' : Store H} {f f' : Frame} {c c' : List Admin}
    (he : Exits o c) (h : Step P host ⟨s, f, c⟩ ⟨s', f', c'⟩) :
    s' = s ∧ f' = f ∧ Exits o c' ∧ Sim.codeSize c' < Sim.codeSize c := by
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩
  · have h' : Step P host ⟨s, f, vals vs⟩ ⟨s', f', c'⟩ := (show c = vals vs from he) ▸ h
    exact (not_step_vals h').elim
  · obtain ⟨x, rest, -, rfl⟩ := he
    exact (not_step_blocked (Or.inl ⟨x, rfl⟩) h).elim
  · obtain ⟨rest, rfl⟩ := he
    exact (not_step_blocked (Or.inr (Or.inl rfl)) h).elim
  · obtain ⟨vs, rest, rfl⟩ := he
    exact exits_trap_step h
  · obtain ⟨vs, rest, rfl⟩ := he
    exact exits_throw_step h
  · obtain ⟨hr, rest, rfl⟩ := he
    exact (not_step_blocked (Or.inr (Or.inr hr)) (tail_code vs a r rest ▸ h)).elim

/-! ## Safety after one step -/

/-- A safe configuration stays safe after any step: an exit that still steps is a
trap or an exception, which keeps its outcome, store and frame. -/
theorem Safe.step_inv {Q : Post H} {n : Nat} {c c' : Config H}
    (h : Safe P host Q (n + 1) c) (hst : Step P host c c') : Safe P host Q n c' := by
  rcases h with ⟨o, he, hq⟩ | ⟨-, hs⟩
  · rcases c with ⟨s, f, code⟩
    rcases c' with ⟨s', f', code'⟩
    obtain ⟨rfl, rfl, he', -⟩ := he.step hst
    exact Safe.of_exits he' hq
  · exact hs c' hst

/-- A safe configuration that cannot step has exited. -/
theorem Safe.exit_of_stuck {Q : Post H} {n : Nat} {c : Config H}
    (h : Safe P host Q (n + 1) c) (hn : ∀ c', ¬ Step P host c c') :
    ∃ o, Exits o c.code ∧ Q c.store c.frame o := by
  rcases h with h | ⟨⟨c', hc'⟩, -⟩
  · exact h
  · exact (hn c' hc').elim

theorem HWP.step_inv {s s' : Store H} {f f' : Frame} {c c' : List Admin} {Q : Post H}
    (h : HWP P host s f c Q) (hst : Step P host ⟨s, f, c⟩ ⟨s', f', c'⟩) : HWP P host s' f' c' Q :=
  fun n => (h (n + 1)).step_inv hst

/-- A step forward. -/
theorem HWP.of_step {s : Store H} {f : Frame} {c : List Admin} {Q : Post H}
    (hp : ∃ c', Step P host ⟨s, f, c⟩ c')
    (hs : ∀ c', Step P host ⟨s, f, c⟩ c' → HWP P host c'.store c'.frame c'.code Q) :
    HWP P host s f c Q
  | 0 => trivial
  | n + 1 => Safe.of_step hp fun c' h => hs c' h n

end Silmaril.Wasm.Logic.Hoare
