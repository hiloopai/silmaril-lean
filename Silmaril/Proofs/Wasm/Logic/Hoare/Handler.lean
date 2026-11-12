module

public import Silmaril.Proofs.Wasm.Logic.Hoare.Label
public import Silmaril.Wasm.Execution.Core.Sim.Closure.HandlerInv

/-!
# The every-run logic: exception handlers

`Safe.handler`: if the body `b` of `HANDLER_m{cs}`, sitting on the values `us`, is
safe with `handlerPost cs (prePost us Q)` (an escaping exception is dispatched to
the catch clauses by `Silmaril.Wasm.Logic.Core.catchPost`), then
`vals us ++ [HANDLER_m{cs} b]` is safe with `Q`. The steps of a handler are
classified by silmaril-lean's `Sim.Step.handler_inv`; the steps of a handler
around a bare `trap` or exception are inverted through the host-free head
relation `Silmaril.Wasm.SingleThreaded.Det.Head`.

A Silmaril addition. The family-absurdity tactic `head_absurd` follows the local
`not_block_family` macro of `Silmaril/Wasm/SingleThreaded/HeadInversion.lean`
(pinned silmaril-lean).
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Hoare

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded (decompose?)
open Silmaril.Wasm.SingleThreaded.Det (Head famOf famOf_of_shape)
open Silmaril.Wasm.Logic.Core (Outcome Post handlerPost catchPost caughtPost)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Codes that are not each other -/

theorem fnv_throwing (a : Nat) :
    SingleThreaded.Det.fnv (throwing a) = ([.ref (.exn a)], [.plain .throwRef]) :=
  fnv_vals_cons (vs := [.ref (.exn a)]) (rest := []) rfl

theorem throwing_ne_vals {a : Nat} {vs : List Val} (h : throwing a = vals vs) : False := by
  have := congrArg SingleThreaded.Det.fnv h
  simp at this

theorem throwing_ne_head {a : Nat} {vs : List Val} {e : Admin} {rest : List Admin}
    (h : throwing a = vals vs ++ [e] ++ rest) (he : e.val? = none) (hne : e ≠ .plain .throwRef) :
    False := by
  have h' : SingleThreaded.Det.fnv (throwing a) = SingleThreaded.Det.fnv (vals vs ++ e :: rest) := by
    rw [h]; simp
  rw [fnv_throwing, fnv_vals_cons he] at h'
  exact hne (List.cons.inj (Prod.mk.inj h').2).1.symm

theorem fnv_trap : SingleThreaded.Det.fnv [Admin.trap] = ([], [.trap]) :=
  fnv_vals_cons (vs := []) (rest := []) rfl

theorem trap_ne_vals {vs : List Val} (h : [Admin.trap] = vals vs) : False := by
  have := congrArg SingleThreaded.Det.fnv h
  simp at this

theorem trap_ne_head {vs : List Val} {e : Admin} {rest : List Admin}
    (h : [Admin.trap] = vals vs ++ [e] ++ rest) (he : e.val? = none) (hne : e ≠ .trap) : False := by
  have h' : SingleThreaded.Det.fnv [Admin.trap] = SingleThreaded.Det.fnv (vals vs ++ e :: rest) := by
    rw [h]; simp
  rw [fnv_trap, fnv_vals_cons he] at h'
  exact hne (List.cons.inj (Prod.mk.inj h').2).1.symm

theorem rcr_ne_throwRef {c : Admin} (hc : c.IsReturnCallRef) : c ≠ .plain .throwRef := by
  rintro rfl; exact hc

theorem rcr_ne_trap {c : Admin} (hc : c.IsReturnCallRef) : c ≠ .trap := by
  rintro rfl; exact hc

/-- Close a `Det.Head` case whose left-hand side cannot be the one at hand. -/
local macro "head_absurd" : tactic => `(tactic| (exfalso; first
  | exact absurd (famOf_of_shape (SingleThreaded.Det.ParametricStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.NumericStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.VectorStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.VariableStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.TableStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.MemoryStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.RefStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.AggregateStep.shape ‹_›)).2 (by simp [famOf])
  | (simp only [Admin.IsCallRef] at *; done)
  | exact SingleThreaded.Det.not_step_throwing ‹_›
  | exact SingleThreaded.Det.not_step_trap ‹_›
  | exact throwing_ne_vals ‹_›
  | exact trap_ne_vals ‹_›
  | exact throwing_ne_head ‹_› (by rfl) (by simp)
  | exact trap_ne_head ‹_› (by rfl) (by simp)
  | exact throwing_ne_head ‹_› (SingleThreaded.val?_returnCallRef ‹_›) (rcr_ne_throwRef ‹_›)
  | exact trap_ne_head ‹_› (SingleThreaded.val?_returnCallRef ‹_›) (rcr_ne_trap ‹_›)))

/-! ## Steps of a handler around a bare trap or exception -/

/-- What a caught exception `a` reduces to at the clause `c`. -/
def Caught (s : Store H) (a : Nat) : Catch → List Admin → Prop
  | .catch_ _ l, code => ∃ e : ExnInst, s.exns[a]? = some e ∧ code = vals e.fields ++ [.plain (.br l)]
  | .catchRef _ l, code => ∃ e : ExnInst, s.exns[a]? = some e ∧
      code = vals e.fields ++ [.ref (.exn a), .plain (.br l)]
  | .catchAll l, code => code = [.plain (.br l)]
  | .catchAllRef l, code => code = [.ref (.exn a), .plain (.br l)]

/-- The reducts of `HANDLER_m{cs} (throw a)`. -/
def ThrowRed (s : Store H) (f : Frame) (m : Nat) (a : Nat) : List Catch → List Admin → Prop
  | [], code => code = throwing a
  | c :: cs, code => (¬ CatchMatches s f a c ∧ code = [.handler m cs (throwing a)]) ∨
      (CatchMatches s f a c ∧ Caught s a c code)

theorem head_handler_throw {s : Store H} {f : Frame} {args : List Val} {m : Nat}
    {cs : List Catch} {a : Nat} {c₀ : Config H}
    (h : Head P s f args (.handler m cs (throwing a)) c₀) :
    args = [] ∧ c₀.store = s ∧ c₀.frame = f ∧ ThrowRed s f m a cs c₀.code := by
  cases h with
  | throwRefHandlerEmpty => exact ⟨rfl, rfl, rfl, rfl⟩
  | throwRefHandlerCatch he ht => exact ⟨rfl, rfl, rfl, .inr ⟨⟨_, _, he, ht, rfl⟩, _, he, rfl⟩⟩
  | throwRefHandlerCatchRef he ht => exact ⟨rfl, rfl, rfl, .inr ⟨⟨_, _, he, ht, rfl⟩, _, he, rfl⟩⟩
  | throwRefHandlerCatchAll => exact ⟨rfl, rfl, rfl, .inr ⟨trivial, rfl⟩⟩
  | throwRefHandlerCatchAllRef => exact ⟨rfl, rfl, rfl, .inr ⟨trivial, rfl⟩⟩
  | throwRefHandlerNext hm => exact ⟨rfl, rfl, rfl, .inl ⟨hm, rfl⟩⟩
  | _ => head_absurd

theorem head_handler_trap {s : Store H} {f : Frame} {args : List Val} {m : Nat}
    {cs : List Catch} {c₀ : Config H} (h : Head P s f args (.handler m cs [.trap]) c₀) :
    args = [] ∧ c₀ = ⟨s, f, [.trap]⟩ := by
  cases h with
  | trapHandler => exact ⟨rfl, rfl⟩
  | _ => head_absurd

/-- A step of a handler whose body has no host-call redex is a host-free head step. -/
theorem step_handler_head {s : Store H} {f : Frame} {m : Nat} {cs : List Catch}
    {b : List Admin} {c' : Config H} (hb : decompose? s b = none)
    (h : Step P host ⟨s, f, [.handler m cs b]⟩ c') : ∃ c₀, Head P s f [] (.handler m cs b) c₀ ∧
      c' = c₀ := by
  have hd : decompose? s [.handler m cs b] = none :=
    SingleThreaded.decompose?_none_of_noRedex (SingleThreaded.noRedex_handler hb)
  obtain ⟨vs, args, c₀, hva, hh, rfl⟩ :=
    SingleThreaded.hostFree_head_inv (W := []) (rest := []) rfl (by simp) (by simp)
      (step_noHost hd h)
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hva.symm
  exact ⟨c₀, hh, by simp⟩

theorem decompose?_throwing (s : Store H) (a : Nat) : decompose? s (throwing a) = none :=
  SingleThreaded.decompose?_vals_cons_none (vs := [.ref (.exn a)]) (r := []) rfl
    fun _ _ => SingleThreaded.decompHead_plain rfl

theorem decompose?_trap (s : Store H) : decompose? s [.trap] = none :=
  SingleThreaded.decompose?_vals_cons_none (vs := []) (r := []) rfl
    fun _ _ => SingleThreaded.decompHead_trap

/-! ## Handlers -/

theorem handlerPost_of_ne_throw {cs : List Catch} {Q : Post H} {s : Store H} {f : Frame}
    {o : Outcome} (hn : ∀ a, o ≠ .throw a) (h : handlerPost cs Q s f o) : Q s f o := by
  cases o with
  | throw a => exact (hn a rfl).elim
  | _ => exact h

/-- A blocked kernel: `br`, `return` or `return_call_ref`. -/
def Kernel (k : List Admin) : Prop :=
  (∃ l, k = [.plain (.br l)]) ∨ k = [.plain .return_] ∨ ∃ c : Admin, c.IsReturnCallRef ∧ k = [c]

/-- The exit of a body ending in a kernel, and the same exit after bubbling. -/
theorem kernel_exit {o : Outcome} {vs : List Val} {k rest : List Admin} (us : List Val)
    (hk : Kernel k) (he : Exits o (vals vs ++ k ++ rest)) :
    (∀ a, o ≠ .throw a) ∧ Exits (o.prepend us) (vals us ++ (vals vs ++ k)) := by
  rcases hk with ⟨l, rfl⟩ | rfl | ⟨c, hc, rfl⟩
  · have ho : o = .br l.toNat vs := exits_br_inv (by simpa using he)
    subst ho
    exact ⟨fun _ h => Outcome.noConfusion h, l, [], rfl, by simp⟩
  · have ho : o = .ret vs := exits_ret_inv (by simpa using he)
    subst ho
    exact ⟨fun _ h => Outcome.noConfusion h, [], by simp⟩
  · obtain ⟨vs₀, a, rfl, rfl⟩ := exits_rcr_inv hc (by simpa using he)
    exact ⟨fun _ h => Outcome.noConfusion h, hc, [], by simp [vals, Val.toAdmin]⟩

theorem kernel_stuck {s : Store H} {f : Frame} {vs : List Val} {k rest : List Admin}
    {c' : Config H} (hk : Kernel k) : ¬ Step P host ⟨s, f, vals vs ++ k ++ rest⟩ c' := by
  rcases hk with ⟨l, rfl⟩ | rfl | ⟨c, hc, rfl⟩
  · simpa using not_step_blocked (Or.inl ⟨l, rfl⟩)
  · simpa using not_step_blocked (Or.inr (Or.inl rfl))
  · simpa using not_step_blocked (Or.inr (Or.inr hc))

/-- A bare trap or exception is not a kernel. -/
theorem kernel_ne_bubble {b : List Admin} {vs : List Val} {k rest : List Admin}
    (hb : b = [.trap] ∨ ∃ a, b = throwing a) (hk : Kernel k) (hv : b = vals vs ++ k ++ rest) :
    False := by
  rcases hk with ⟨l, rfl⟩ | rfl | ⟨c, hc, rfl⟩ <;> rcases hb with rfl | ⟨a, rfl⟩
  · exact trap_ne_head hv rfl (by simp)
  · exact throwing_ne_head hv rfl (by simp)
  · exact trap_ne_head hv rfl (by simp)
  · exact throwing_ne_head hv rfl (by simp)
  · exact trap_ne_head hv (SingleThreaded.val?_returnCallRef hc) (rcr_ne_trap hc)
  · exact throwing_ne_head hv (SingleThreaded.val?_returnCallRef hc) (rcr_ne_throwRef hc)

section Handler

variable {m : Nat} {us : List Val} {Q : Post H}

theorem handler_ctxt {s s' : Store H} {f f' : Frame} {cs : List Catch} {b b' : List Admin}
    (h : Step P host ⟨s, f, b⟩ ⟨s', f', b'⟩) :
    Step P host ⟨s, f, vals us ++ [.handler m cs b]⟩ ⟨s', f', vals us ++ [.handler m cs b']⟩ :=
  Sim.Step.vals_left (Step.ctxtHandler h) us

/-- A step of a handler around a bare trap or exception, under values. -/
theorem handler_kernel_inv {s s' : Store H} {f f' : Frame} {cs : List Catch} {b es' : List Admin}
    (hb : b = [.trap] ∨ ∃ a, b = throwing a)
    (h : Step P host ⟨s, f, vals us ++ [.handler m cs b]⟩ ⟨s', f', es'⟩) :
    ∃ is', Step P host ⟨s, f, [.handler m cs b]⟩ ⟨s', f', is'⟩ ∧ es' = vals us ++ is' := by
  obtain ⟨is', hi, rfl⟩ := Sim.Step.handler_inv h
  rcases hi with ⟨b', hs, -⟩ | ⟨-, -, vs, hv, -⟩ | ⟨-, -, vs, k, rest, hk, hv, -⟩ | ⟨-, hs⟩
  · rcases hb with rfl | ⟨a, rfl⟩
    · exact (not_step_trap hs).elim
    · exact (not_step_throwing hs).elim
  · rcases hb with rfl | ⟨a, rfl⟩
    · exact (trap_ne_vals hv).elim
    · exact (throwing_ne_vals hv).elim
  · exact (kernel_ne_bubble hb hk hv).elim
  · exact ⟨is', hs, rfl⟩

/-- A caught exception branches to its clause's label. -/
theorem caught_safe {n : Nat} {s : Store H} {f : Frame} {a : Nat} {c : Catch} {code : List Admin}
    (hc : Caught s a c code) (hq : caughtPost s f a (prePost us Q) c) :
    Safe P host Q n ⟨s, f, vals us ++ code⟩ := by
  rcases c with ⟨x, l⟩ | ⟨x, l⟩ | l | l
  · obtain ⟨e, he, rfl⟩ := hc
    obtain ⟨e', he', hq⟩ := hq
    obtain rfl : e' = e := Option.some.inj (he'.symm.trans he)
    exact Safe.of_exits (o := .br l.toNat (us ++ e'.fields)) ⟨l, [], rfl, by simp⟩ hq
  · obtain ⟨e, he, rfl⟩ := hc
    obtain ⟨e', he', hq⟩ := hq
    obtain rfl : e' = e := Option.some.inj (he'.symm.trans he)
    exact Safe.of_exits (o := .br l.toNat (us ++ (e'.fields ++ [Val.ref (.exn a)])))
      ⟨l, [], rfl, by simp [vals, Val.toAdmin]⟩ hq
  · obtain rfl := hc
    exact Safe.of_exits (o := .br l.toNat (us ++ [])) ⟨l, [], rfl, by simp⟩ hq
  · obtain rfl := hc
    exact Safe.of_exits (o := .br l.toNat (us ++ [Val.ref (.exn a)]))
      ⟨l, [], rfl, by simp [vals, Val.toAdmin]⟩ hq

/-- The dispatch of an exception to the clauses can step. -/
theorem handler_throw_progress {s : Store H} {f : Frame} {a : Nat} {cs : List Catch}
    (hq : catchPost s f a (prePost us Q) cs) :
    ∃ c', Step P host ⟨s, f, [.handler m cs (throwing a)]⟩ c' := by
  rcases cs with _ | ⟨c, cs⟩
  · exact ⟨_, Step.throwRefHandlerEmpty⟩
  rcases hq with ⟨hm, -⟩ | ⟨hm, -⟩
  · rcases c with ⟨x, l⟩ | ⟨x, l⟩ | l | l
    · obtain ⟨e, ta, he, ht, rfl⟩ := hm
      exact ⟨_, Step.throwRefHandlerCatch he ht⟩
    · obtain ⟨e, ta, he, ht, rfl⟩ := hm
      exact ⟨_, Step.throwRefHandlerCatchRef he ht⟩
    · exact ⟨_, Step.throwRefHandlerCatchAll⟩
    · exact ⟨_, Step.throwRefHandlerCatchAllRef⟩
  · exact ⟨_, Step.throwRefHandlerNext hm⟩

/-- One step of the dispatch of an exception to the clauses. -/
theorem handler_throw_succ {n : Nat} {s s' : Store H} {f f' : Frame} {cs : List Catch} {a : Nat}
    {is' : List Admin}
    (ih : ∀ cs', catchPost s f a (prePost us Q) cs' →
      Safe P host Q n ⟨s, f, vals us ++ [.handler m cs' (throwing a)]⟩)
    (hq : catchPost s f a (prePost us Q) cs)
    (hst : Step P host ⟨s, f, [.handler m cs (throwing a)]⟩ ⟨s', f', is'⟩) :
    Safe P host Q n ⟨s', f', vals us ++ is'⟩ := by
  obtain ⟨c₀, hh, he⟩ := step_handler_head (decompose?_throwing s a) hst
  obtain ⟨-, hs, hf, hr⟩ := head_handler_throw hh
  obtain ⟨rfl, rfl, rfl⟩ : s' = s ∧ f' = f ∧ is' = c₀.code := by
    subst he; exact ⟨hs, hf, rfl⟩
  rcases cs with _ | ⟨c, cs⟩
  · exact Safe.of_exits (o := .throw a) ⟨us, [], by rw [show c₀.code = throwing a from hr]; simp⟩ hq
  · rcases hr with ⟨hm, hcode⟩ | ⟨hm, hc⟩ <;> rcases hq with ⟨hm', hq⟩ | ⟨hm', hq⟩
    · exact (hm hm').elim
    · exact hcode ▸ ih cs hq
    · exact caught_safe hc hq
    · exact (hm' hm).elim

/-- An exception thrown into a handler is safe when the dispatch postcondition
holds. -/
theorem handler_throw_safe : ∀ (n : Nat) (cs : List Catch) {s : Store H} {f : Frame} {a : Nat},
    catchPost s f a (prePost us Q) cs →
    Safe P host Q n ⟨s, f, vals us ++ [.handler m cs (throwing a)]⟩
  | 0, _, _, _, _, _ => trivial
  | n + 1, cs, s, f, a, hq => by
    obtain ⟨c', hc'⟩ := handler_throw_progress (P := P) (host := host) (m := m) hq
    rcases c' with ⟨s₁, f₁, is₁⟩
    refine Safe.of_step ⟨_, Sim.Step.vals_left hc' us⟩ fun ⟨s', f', es'⟩ hst => ?_
    obtain ⟨is', hs, rfl⟩ := handler_kernel_inv (Or.inr ⟨a, rfl⟩) hst
    exact handler_throw_succ (fun cs' h => handler_throw_safe n cs' h) hq hs

/-- A trap inside a handler. -/
theorem handler_trap_succ {n : Nat} {s s' : Store H} {f f' : Frame} {cs : List Catch}
    {is' : List Admin} (hq : Q s f .trap)
    (hst : Step P host ⟨s, f, [.handler m cs [.trap]]⟩ ⟨s', f', is'⟩) :
    Safe P host Q n ⟨s', f', vals us ++ is'⟩ := by
  obtain ⟨c₀, hh, he⟩ := step_handler_head (decompose?_trap s) hst
  obtain ⟨-, rfl⟩ := head_handler_trap hh
  obtain ⟨rfl, rfl, rfl⟩ : s' = s ∧ f' = f ∧ is' = [.trap] := by
    simp only [Config.mk.injEq] at he; exact he
  exact Safe.of_exits (o := .trap) ⟨us, [], rfl⟩ hq

/-- A handler around a trap or an exception that is still inside a sequence steps. -/
theorem handler_progress_cut {s : Store H} {f : Frame} {cs : List Catch} {vs : List Val}
    {k₀ rest : List Admin} (hk : k₀ = [.trap] ∨ ∃ a, k₀ = throwing a) (hne : vs ≠ [] ∨ rest ≠ []) :
    ∃ c', Step P host ⟨s, f, vals us ++ [.handler m cs (vals vs ++ k₀ ++ rest)]⟩ c' := by
  rcases hk with rfl | ⟨a, rfl⟩
  · exact ⟨_, handler_ctxt (Step.trapInstrs hne)⟩
  · exact ⟨_, handler_ctxt (Step.throwRefInstrs hne)⟩

/-- A tail call leaves a handler. -/
theorem handler_progress_tail {s : Store H} {f : Frame} {cs : List Catch} {vs : List Val}
    {a : Nat} {r : Admin} {rest : List Admin} (hr : r.IsReturnCallRef) :
    ∃ c', Step P host ⟨s, f, vals us ++ [.handler m cs (vals vs ++ .ref (.func a) :: r :: rest)]⟩ c' := by
  have hs : Step P host ⟨s, f, [.handler m cs (vals (vs ++ [.ref (.func a)]) ++ [r] ++ rest)]⟩
      ⟨s, f, vals (vs ++ [.ref (.func a)]) ++ [r]⟩ := Step.returnCallRefHandler hr
  rw [List.append_assoc, List.singleton_append, ← tail_code] at hs
  exact ⟨_, Sim.Step.vals_left hs us⟩

/-- A handler whose body has exited can step. -/
theorem handler_progress {s : Store H} {f : Frame} {cs : List Catch} {b : List Admin}
    {o : Outcome} (he : Exits o b) (hq : handlerPost cs (prePost us Q) s f o) :
    ∃ c', Step P host ⟨s, f, vals us ++ [.handler m cs b]⟩ c' := by
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩
  · exact ⟨_, Sim.Step.vals_left ((show b = vals vs from he) ▸ Step.handlerVals) us⟩
  · obtain ⟨x, rest, -, rfl⟩ := he
    exact ⟨_, Sim.Step.vals_left (by simpa using Step.brHandler (rest := rest)) us⟩
  · obtain ⟨rest, rfl⟩ := he
    exact ⟨_, Sim.Step.vals_left (by simpa using Step.returnHandler (rest := rest)) us⟩
  · obtain ⟨vs, rest, rfl⟩ := he
    rcases trap_shape_cases vs rest with ⟨rfl, rfl⟩ | hne
    · exact ⟨_, Sim.Step.vals_left Step.trapHandler us⟩
    · simpa using handler_progress_cut (vs := vs) (rest := rest) (Or.inl rfl) hne
  · obtain ⟨vs, rest, rfl⟩ := he
    rcases trap_shape_cases vs rest with ⟨rfl, rfl⟩ | hne
    · obtain ⟨⟨s₁, f₁, is₁⟩, hc'⟩ := handler_throw_progress (P := P) (host := host) (m := m) hq
      exact ⟨_, Sim.Step.vals_left hc' us⟩
    · exact handler_progress_cut (Or.inr ⟨a, rfl⟩) hne
  · obtain ⟨hr, rest, rfl⟩ := he
    exact handler_progress_tail hr

/-- A handler whose body can step, or has exited, can step. -/
theorem handler_progress' {n : Nat} {s : Store H} {f : Frame} {cs : List Catch} {b : List Admin}
    (h : Safe P host (handlerPost cs (prePost us Q)) (n + 1) ⟨s, f, b⟩) :
    ∃ c', Step P host ⟨s, f, vals us ++ [.handler m cs b]⟩ c' := by
  rcases h with ⟨o, he, hq⟩ | ⟨⟨⟨s', f', b'⟩, hb⟩, -⟩
  · exact handler_progress he hq
  · exact ⟨_, handler_ctxt hb⟩

/-- A body that fell through, or ended in a kernel. -/
theorem handler_kernel {n : Nat} {s : Store H} {f : Frame} {cs : List Catch} {vs : List Val}
    {k rest : List Admin} (hk : Kernel k)
    (h : Safe P host (handlerPost cs (prePost us Q)) (n + 1) ⟨s, f, vals vs ++ k ++ rest⟩) :
    Safe P host Q n ⟨s, f, vals us ++ (vals vs ++ k)⟩ := by
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => kernel_stuck hk)
  obtain ⟨hn, he'⟩ := kernel_exit us hk he
  exact Safe.of_exits he' (handlerPost_of_ne_throw (Q := prePost us Q) hn hq)

theorem handler_values {n : Nat} {s : Store H} {f : Frame} {cs : List Catch} {vs : List Val}
    (h : Safe P host (handlerPost cs (prePost us Q)) (n + 1) ⟨s, f, vals vs⟩) :
    Safe P host Q n ⟨s, f, vals us ++ vals vs⟩ := by
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => not_step_vals)
  have ho : o = .normal vs := exits_vals_inv he
  subst ho
  exact Safe.of_exits (o := .normal (us ++ vs)) (by simp [Exits, vals]) hq

/-- A bare trap or exception in the body. -/
theorem handler_bubble {n : Nat} {s s' : Store H} {f f' : Frame} {cs : List Catch}
    {b is' : List Admin} (hb : b = [.trap] ∨ ∃ a, b = throwing a)
    (h : Safe P host (handlerPost cs (prePost us Q)) (n + 1) ⟨s, f, b⟩)
    (hst : Step P host ⟨s, f, [.handler m cs b]⟩ ⟨s', f', is'⟩) :
    Safe P host Q n ⟨s', f', vals us ++ is'⟩ := by
  rcases hb with rfl | ⟨a, rfl⟩
  · obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => not_step_trap)
    have ho : o = .trap := exits_trap_inv (vs := []) (rest := []) he
    subst ho
    exact handler_trap_succ hq hst
  · obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => not_step_throwing)
    have ho : o = .throw a := exits_throw_inv (vs := []) (rest := []) (by simpa using he)
    subst ho
    exact handler_throw_succ (fun cs' h => handler_throw_safe n cs' h) hq hst

/-- The steps of a handler, read off the body. -/
theorem handler_succ {n : Nat} {s : Store H} {f : Frame} {cs : List Catch} {b : List Admin}
    {c' : Config H}
    (ih : ∀ s f b, Safe P host (handlerPost cs (prePost us Q)) n ⟨s, f, b⟩ →
      Safe P host Q n ⟨s, f, vals us ++ [.handler m cs b]⟩)
    (h : Safe P host (handlerPost cs (prePost us Q)) (n + 1) ⟨s, f, b⟩)
    (hst : Step P host ⟨s, f, vals us ++ [.handler m cs b]⟩ c') : Safe P host Q n c' := by
  rcases c' with ⟨s', f', es'⟩
  obtain ⟨is', hi, rfl⟩ := Sim.Step.handler_inv hst
  rcases hi with ⟨b', hs, rfl⟩ | ⟨rfl, rfl, vs, rfl, rfl⟩ | ⟨rfl, rfl, vs, k, rest, hk, rfl, rfl⟩ |
      ⟨hb, hs⟩
  · exact ih _ _ _ (h.step_inv hs)
  · exact handler_values h
  · exact handler_kernel hk h
  · exact handler_bubble hb h hs

/-- **Exception handlers.** If the body is safe with `handlerPost cs (prePost us Q)`,
so is the handler, with `Q`. -/
theorem Safe.handler : ∀ {n : Nat} {s : Store H} {f : Frame} {cs : List Catch} {b : List Admin},
    Safe P host (handlerPost cs (prePost us Q)) n ⟨s, f, b⟩ →
    Safe P host Q n ⟨s, f, vals us ++ [.handler m cs b]⟩
  | 0, _, _, _, _, _ => trivial
  | _ + 1, _, _, _, _, h =>
    Safe.of_step (handler_progress' h) fun _ hst =>
      handler_succ (fun _ _ _ => Safe.handler) h hst

end Handler

/-- **Exception handlers** for every-run weakest preconditions. -/
theorem HWP.handler {s : Store H} {f : Frame} {m : Nat} {cs : List Catch} {us : List Val}
    {b : List Admin} {Q : Post H} (h : HWP P host s f b (handlerPost cs (prePost us Q))) :
    HWP P host s f (vals us ++ [.handler m cs b]) Q :=
  fun n => Safe.handler (h n)

end Silmaril.Wasm.Logic.Hoare
