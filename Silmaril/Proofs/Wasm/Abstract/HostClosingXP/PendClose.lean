module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.PendReach
public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.BackGoal

/-!
# Pending calls and trapping behaviours of the canonical closure (proofs)

The pending host calls of `wasmEvPendXP` are read through the closure itself:

* `pendLXP_trap`: a pending call `(cs, m)` of a typed invocation, answered by a trap in its own
  store, is a trapping behaviour `(cs ++ [⟨m, (m.2.1, trap)⟩], trap)` of the closure: a descent
  cuts the reached call (`reachLXP_cut`) and resolves it by the callee's trap
  (`Shape.Subst.intTrap`); a frame-level tail call resolves the tail call the same way;
* `close_pend`: conversely, in every behaviour of the closure, the log before a host event is a
  pending call of that event's call (least-fixpoint induction: an event of a Wasm body's
  resolution lies in the behaviour of some logged callee, reached by `reachLXP_of_log`, or of the
  frame's tail callee).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type}

/-- The host event answering the call `m` by a trap, in its store. -/
abbrev trapEv (m : (wasmHostSig H).Op) : Call (wasmHostSig H) := ⟨m, (m.2.1, .trap)⟩

/-! ## Pending calls are trapping behaviours -/

/-- **A pending call answered by a trap is a trapping behaviour of the closure.** -/
theorem pendLXP_trap {s : Store H} {a : Nat} {vs : List Val} {cs : List (Call (wasmHostSig H))}
    {m : (wasmHostSig H).Op} (h : PendLXP s a vs cs m) :
    ∀ {fi : FuncInst H} {ps rs : List Validation.CValType}, s.funcs[a]? = some fi →
      Validation.DefType.funcType? fi.type = some (ps, rs) →
      (cs ++ [trapEv m], .trap) ∈ Cl a s vs := by
  induction h with
  | @self s a vs fi hh hf hcode =>
    intro fi' ps rs hf' hty
    obtain rfl : fi = fi' := Option.some.inj (hf.symm.trans hf')
    exact close_hostX (s' := s) (r := .trap) (fl := .trap) hf hcode hty rfl
  | @desc s a vs fi fn l q q' z m hf hcode hr hq _ ih =>
    intro fi' ps rs hf' hty
    obtain rfl : fi = fi' := Option.some.inj (hf.symm.trans hf')
    obtain ⟨fz, psz, rsz, hfz, htyz⟩ := reachLXP_typed hr
    have hz := ih hfz htyz
    obtain ⟨ws, f', d⟩ := reachLXP_cut hr
    refine close_of_open (.inl ⟨fi, fn, ps, rs, z.2.2, f', .trap, .trap, _, hf, hcode, hty, d, rfl,
      rfl⟩) ?_
    rw [List.map_append, List.map_cons, List.map_nil]
    have := subst_pre_then hq (Shape.Subst.intTrap (c := Cl) (rest := []) (e := endOfFlow Flow.trap z.2.2)
      (ans := (Sum.inl ws, z.2.2)) hz)
    simpa [OCall.mk, OCall.lift, List.append_assoc] using this
  | @tail s s₁ a vs fi fn f₂ a' n args l q q' m hf hcode hbody hq _ ih =>
    intro fi' ps rs hf' hty
    obtain rfl : fi = fi' := Option.some.inj (hf.symm.trans hf')
    obtain ⟨fz, psz, rsz, hfz, htyz, -⟩ := evalLXPh_tail_wf hbody a' args n rfl
    have := close_wasm_tailTrap hf hcode hty hbody hq (ih hfz htyz)
    simpa [List.append_assoc] using this

/-! ## Prefixes of host events are pending calls -/

/-- **An event of a resolution of internal calls comes from a callee**: a prefix of the calls
resolved, then a callee behaviour containing the event. -/
theorem subst_split {c : (wasmHShape H).ClosedMod} {e₀ : End (Store H) (List Val ⊕ Nat)} :
    ∀ (L : List (OCall H)) {y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)},
      Shape.Subst c (L.map OCall.lift) e₀ y →
      ∀ (u w : List (Call (wasmHostSig H))) (e : Call (wasmHostSig H)), y.1 = u ++ e :: w →
      ∃ (L₁ L₂ : List (OCall H)) (g : Nat) (args : List Val) (s₁ s₂ : Store H)
        (b : List Val ⊕ Nat) (q₁ c₁ u₂ w' : List (Call (wasmHostSig H)))
        (e' : End (Store H) (List Val ⊕ Nat)),
        L = L₁ ++ OCall.mk g args s₁ b s₂ :: L₂ ∧ Shape.SubstPre c (L₁.map OCall.lift) q₁ ∧
        (c₁, e') ∈ c g s₁ args ∧ c₁ = u₂ ++ e :: w' ∧ u = q₁ ++ u₂ := by
  intro L
  induction L with
  | nil =>
    intro y hs u w e hy
    cases hs
    simp at hy
  | cons z L ih =>
    intro y hs u w e hy
    rcases z with ⟨⟨⟨⟩⟩ | ⟨g, args, s₁⟩, b, s₂⟩
    change Shape.Subst c (⟨.inr ⟨g, (args, s₁)⟩, (b, s₂)⟩ :: L.map OCall.lift) e₀ y at hs
    cases hs with
    | @int _ _ _ _ _ _ _ c₁ y' hm hrest =>
      rcases psplit_app hy with ⟨w', h₁⟩ | ⟨u', rfl, h₁⟩
      · exact ⟨[], L, g, args, s₁, s₂, b, [], c₁, u, w', _, rfl, .nil, hm, h₁, rfl⟩
      · obtain ⟨L₁, L₂, g', args', s₁', s₂', b', q₁, c₂, u₂, w', e', rfl, hq, hm', hc, rfl⟩ :=
          ih hrest u' w e h₁
        exact ⟨OCall.mk g args s₁ b s₂ :: L₁, L₂, g', args', s₁', s₂', b', c₁ ++ q₁, c₂, u₂, w',
          e', rfl, .int hm hq, hm', hc, by simp⟩
    | intTrap hm =>
      exact ⟨[], L, g, args, s₁, s₂, b, [], _, u, w, _, rfl, .nil, hm, hy, rfl⟩
    | intDiv hm =>
      exact ⟨[], L, g, args, s₁, s₂, b, [], _, u, w, _, rfl, .nil, hm, hy, rfl⟩

/-- The behaviours of the closure whose host events are preceded by pending calls. -/
def PendC : (wasmHShape H).ClosedMod := fun a s vs =>
  {y | y ∈ Cl a s vs ∧ ∀ (u w : List (Call (wasmHostSig H))) (e : Call (wasmHostSig H)),
    y.1 = u ++ e :: w → PendLXP s a vs u e.1}

theorem pendC_le : PendC (H := H) ≤ Cl := fun _ _ _ _ h => h.1

/-- **In every behaviour of the closure, the log before a host event is a pending call.** -/
theorem close_le_pendC : Cl (H := H) ≤ PendC := by
  refine OrderHom.lfp_le _ ?_
  rintro a s vs y ⟨x, hx, hS⟩
  refine ⟨close_of_open hx (hS.mono pendC_le), ?_⟩
  intro u w e hy
  rcases hx with ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hfi, hc, hty, hE, hxf, rfl⟩ |
    ⟨fi, fn, ps, rs, s₁, s₂, f₂, a', n, args, b₀, l, hfi, hc, hty, hE, rfl⟩ |
    ⟨fi, hh, ps, rs, s', r, fl, hfi, hc, hty, hxf, rfl⟩
  · obtain ⟨L₁, L₂, g, args, t₁, t₂, b, q₁, c₁, u₂, w', e', rfl, hq, hm, rfl, rfl⟩ :=
      subst_split l hS u w e hy
    exact .desc hfi hc (reachLXP_of_log hE L₁ L₂ g args t₁ t₂ b rfl) (substPre_mono pendC_le hq)
      ((hm.2 u₂ w' e rfl))
  · obtain ⟨L₁, L₂, g, args', t₁, t₂, b, q₁, c₁, u₂, w', e', hL, hq, hm, rfl, rfl⟩ :=
      subst_split _ hS u w e hy
    rcases psplit_last hL with ⟨w'', h₁⟩ | ⟨rfl, h₁⟩
    · exact .desc hfi hc (reachLXP_of_log hE L₁ w'' g args' t₁ t₂ b h₁)
        (substPre_mono pendC_le hq) (hm.2 u₂ w' e rfl)
    · obtain ⟨rfl, rfl, rfl⟩ := oCall_mk_inj h₁
      exact .tail hfi hc hE (substPre_mono pendC_le hq) (hm.2 u₂ w' e rfl)
  · cases hS with
    | ext h =>
      cases h
      obtain ⟨rfl, rfl⟩ : u = [] ∧ e = ⟨(hh, s, vs), (s', r)⟩ := by
        rcases u with _ | ⟨_, _⟩
        · simp only [List.nil_append, List.cons.injEq] at hy
          exact ⟨rfl, hy.1.symm⟩
        · simp at hy
      exact .self hfi hc

/-- **The log before a host event of a closed behaviour is a pending call of that event.** -/
theorem close_pend {a : Nat} {s : Store H} {vs : List Val}
    {u w : List (Call (wasmHostSig H))} {e : Call (wasmHostSig H)}
    {r : End (Store H) (List Val ⊕ Nat)} (h : (u ++ e :: w, r) ∈ Cl a s vs) :
    PendLXP s a vs u e.1 :=
  (close_le_pendC a s vs h).2 u w e rfl

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
