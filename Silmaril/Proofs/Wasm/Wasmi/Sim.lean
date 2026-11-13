module

public import Silmaril.Proofs.Wasm.Wasmi.SimRel
public import Silmaril.Proofs.Wasm.Wasmi.LocalGet
public import Silmaril.Wasm.Atlas.Variant.Thms
public import Silmaril.Wasm.Execution.Core.Sim.StepMatch
public import Silmaril.Wasm.Execution.Core.Sim.Segments
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Label
public import Silmaril.Wasm.Execution.Core.Sim.Closure.HandlerInv
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Frame
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Struct

@[expose] public section

/-!
# wasmi's translated code is simulated by the loose model

**Lock-step simulation.** For a host respecting the function relation of the translation
(`HostRespects (FuncRel fuseBI) host`, implied by silmaril-lean's `HostParametric`), every
Core step of a configuration of the translated store is matched by exactly one step of the
loose model (`Loose.Step`) from an `LRel`-related configuration of the source store, with
related results (`sim_main`). The proof is by strong induction on the size of the left code.
The left code is `val* a es`, with `a` its first non-value (`exists_head_of_not_all`); the
right code is `val* R₀` (`LRel.peel`), and

* a `trap` or `THROW_REF` head (`kernel_case`): the same redex on the right
  (`Step.transport_storeRel`, shapes from `Step.trap_redex_aux`/`Step.throwRef_redex_aux`), or
  the same discard of values and of as many following instructions (`trap-instrs`,
  `throw_ref-instrs`), ending in a cut pair;
* a translated pattern (`group_case`): the left reads the local (`Step.localGet_inv`), the
  right takes `selectEither` with the constant `0`;
* a pointwise head (`head_case`): the same code on both sides by silmaril-lean's
  `Step.match_storeRel` (calls into related bodies, host calls through `HostRespects`); a
  structured instruction with related bodies by `struct_match_aux`; a `LABEL`, `HANDLER` or
  `FRAME` with related bodies by the inversions `Step.label_inv`, `Step.handler_inv`,
  `Step.frame_redex_aux`, with the induction hypothesis for steps inside the body and the
  same bubbling rule on the right otherwise.

`behaviours_subset`: hence every Core behaviour of an invocation of the translated store is a
loose behaviour of the same invocation of the source store, divergence included.

New proofs, using silmaril-lean's code-relation kit (`Silmaril/Wasm/Execution/Core/Sim/*`).
-/

namespace Silmaril.Proofs.Wasm.Wasmi

open Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (Ty Expand)
open Silmaril.Wasm.Wasmi Silmaril.Wasm.Atlas.Variant

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The function relation of the translation. -/
abbrev FR : FuncInst H → FuncInst H → Prop := FuncRel fuseBI

/-- The simulation obligation for left code of size below `m`. -/
def SimIH (P : Profile) (host : HostSemantics H) (m : Nat) : Prop :=
  ∀ {sL sL' sR : Store H} {f f' : Frame} {wL wL' R : List Admin}, sizeOf wL < m →
    Execution.Core.Step P host ⟨sL, f, wL⟩ ⟨sL', f', wL'⟩ → StoreRel FR sL sR → LRel wL R →
    ∃ sR' R', Loose.Step P host ⟨sR, f, R⟩ ⟨sR', f', R'⟩ ∧ StoreRel FR sL' sR' ∧ LRel wL' R'

/-! ## Helpers -/

theorem flat_of_isReturnCallRef {c : Admin} (hc : c.IsReturnCallRef) :
    Flat c ∧ ∀ x, c ≠ .plain (.localGet x) := by
  rcases Admin.isReturnCallRef_cases hc with ⟨y, rfl⟩ | ⟨d, rfl⟩ <;>
    exact ⟨trivial, fun x => by simp⟩

/-- An exit shape `val* [k] rest` against related code. -/
theorem exit_inv {vs : List Val} {k : Admin} {rest R : List Admin}
    (h : LRel (vals vs ++ [k] ++ rest) R) (hk : Flat k) (hl : ∀ x, k ≠ .plain (.localGet x)) :
    ∃ R', R = vals vs ++ [k] ++ R' := by
  obtain ⟨R', rfl⟩ := LRel.exit_inv (by simpa using h) hk hl
  exact ⟨R', by simp⟩

/-- A step of the loose model from a Core step. -/
theorem core {c c' : Config H} (h : Execution.Core.Step P host c c') : Loose.Step P host c c' :=
  Or.inl h

/-- A related step on the same code, by silmaril-lean's `Step.match_storeRel`. -/
theorem same_case (hhost : HostRespects FR host) {sL sL' sR : Store H} {f f' : Frame}
    {w w' : List Admin} (hst : StoreRel FR sL sR)
    (hs : Execution.Core.Step P host ⟨sL, f, w⟩ ⟨sL', f', w'⟩) :
    ∃ sR' R', Loose.Step P host ⟨sR, f, w⟩ ⟨sR', f', R'⟩ ∧ StoreRel FR sL' sR' ∧ LRel w' R' := by
  obtain ⟨t', es'', ht, hst', hrel⟩ :=
    Sim.Step.match_storeRel (B := fun _ _ => False) (fun _ _ h => h) hhost hs sR hst
  exact ⟨t', es'', core ht, hst', LRel.ofAdminsRel hrel⟩

theorem sizeOf_label_body (n : Nat) (c : List Instr) (b : List Admin) :
    sizeOf b < sizeOf (Admin.label n c b) := by
  simp only [Admin.label.sizeOf_spec]; omega

theorem sizeOf_handler_body (n : Nat) (cs : List Catch) (b : List Admin) :
    sizeOf b < sizeOf (Admin.handler n cs b) := by
  simp only [Admin.handler.sizeOf_spec]; omega

theorem sizeOf_frame_body (n : Nat) (fi : Frame) (b : List Admin) :
    sizeOf b < sizeOf (Admin.frame n fi b) := by
  simp only [Admin.frame.sizeOf_spec]; omega

/-! ## `LABEL`, `HANDLER` and `FRAME` heads -/

/-- The conclusion of a matched step: a loose step from the right code `R`, related stores and
related results. -/
def Goal (P : Profile) (host : HostSemantics H) (sL' sR : Store H) (f f' : Frame)
    (R wL' : List Admin) : Prop :=
  ∃ sR' R', Loose.Step P host ⟨sR, f, R⟩ ⟨sR', f', R'⟩ ∧ StoreRel FR sL' sR' ∧ LRel wL' R'

/-- An inner step under a context, by the induction hypothesis. -/
theorem wrap_ctxt (wrapL' wrapR wrapR' : List Admin → Admin) {m : Nat} (ih : SimIH P host m)
    {sL sL' sR : Store H} {f₀ f₀' : Frame} {us : List Val} {bL bL' bR : List Admin}
    {g g' : Frame} (hlt : sizeOf bL < m) (hst : StoreRel FR sL sR) (hb : LRel bL bR)
    (h : Execution.Core.Step P host ⟨sL, g, bL⟩ ⟨sL', g', bL'⟩)
    (hwrap : ∀ {s s' R R'}, Loose.Step P host ⟨s, g, R⟩ ⟨s', g', R'⟩ →
      Loose.Step P host ⟨s, f₀, [wrapR R]⟩ ⟨s', f₀', [wrapR' R']⟩)
    (hrel : ∀ {R'}, LRel bL' R' → ARel (wrapL' bL') (wrapR' R')) :
    Goal P host sL' sR f₀ f₀' (vals us ++ [wrapR bR]) (vals us ++ [wrapL' bL']) := by
  obtain ⟨sR', bR', hl, hst', hr⟩ := ih hlt h hst hb
  exact ⟨sR', _, loose_vals_left (hwrap hl) us, hst', LRel.vals_append us (.cons (hrel hr) .nil)⟩

/-- A bubbling rule at an exit shape `val* k rest` of the body: the same rule on the right. -/
theorem exit_wrap (wrap : List Admin → Admin) {sL sR : Store H} {f : Frame} {us vs : List Val}
    {k : Admin} {rest bR out : List Admin} (hst : StoreRel FR sL sR)
    (hb : LRel (vals vs ++ [k] ++ rest) bR) (hk : Flat k) (hl : ∀ x, k ≠ .plain (.localGet x))
    (hstep : ∀ R', Execution.Core.Step P host ⟨sR, f, [wrap (vals vs ++ [k] ++ R')]⟩ ⟨sR, f, out⟩) :
    Goal P host sL sR f f (vals us ++ [wrap bR]) (vals us ++ out) := by
  obtain ⟨R', hR'⟩ : ∃ R', bR = vals vs ++ [k] ++ R' := exit_inv hb hk hl
  rw [hR']
  exact ⟨sR, _, core (Sim.Step.vals_left (hstep R') us), hst, LRel.refl _⟩

/-- A bubbling rule at a body related only to itself (values, a trap, a thrown exception). -/
theorem same_wrap (wrap : List Admin → Admin) {sL sR : Store H} {f : Frame} {us : List Val}
    {bL bR out : List Admin} (hst : StoreRel FR sL sR) (hb : bR = bL)
    (hstep : Execution.Core.Step P host ⟨sR, f, [wrap bL]⟩ ⟨sR, f, out⟩) :
    Goal P host sL sR f f (vals us ++ [wrap bR]) (vals us ++ out) := by
  rw [hb]
  exact ⟨sR, _, core (Sim.Step.vals_left hstep us), hst, LRel.refl _⟩

/-- `br-label-zero`: the right side continues with its own (related) continuation. -/
theorem label_brZero {sL sR : Store H} {f : Frame} {us vs' vs : List Val} {n : Nat}
    {c c' : List Instr} {l : LabelIdx} {rest bR : List Admin} (hst : StoreRel FR sL sR)
    (hc : InstrsRel fuseBI c c') (hb : LRel (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest) bR)
    (hl : l.toNat = 0) (hn : vs.length = n) :
    Goal P host sL sR f f (vals us ++ [.label n c' bR]) (vals us ++ (vals vs ++ expression c)) := by
  obtain ⟨R', hR'⟩ : ∃ R', bR = vals (vs' ++ vs) ++ [.plain (.br l)] ++ R' :=
    exit_inv (k := .plain (.br l)) (by simpa using hb) trivial (fun _ => by simp)
  have hs' : Execution.Core.Step P host ⟨sR, f, [.label n c' bR]⟩ ⟨sR, f, vals vs ++ expression c'⟩ := by
    rw [hR']; simpa using Step.brLabelZero (P := P) (host := host) (s := sR) (f := f)
      (cont := c') (vs' := vs') (vs := vs) (rest := R') hl hn
  exact ⟨sR, _, core (Sim.Step.vals_left hs' us), hst,
    LRel.vals_append us (LRel.vals_append vs (LRel.src hc))⟩

/-- A step at a `LABEL` head with related continuation and body. -/
theorem label_case {n : Nat} {c c' : List Instr} {bL bR : List Admin}
    (ih : SimIH P host (sizeOf (Admin.label n c bL))) {sL sL' sR : Store H} {f f' : Frame}
    {us : List Val} {is' : List Admin} (hst : StoreRel FR sL sR) (hc : InstrsRel fuseBI c c')
    (hb : LRel bL bR)
    (hs : Execution.Core.Step P host ⟨sL, f, vals us ++ [.label n c bL]⟩ ⟨sL', f', is'⟩) :
    Goal P host sL' sR f f' (vals us ++ [.label n c' bR]) is' := by
  obtain ⟨is'', hred, he⟩ : ∃ is'', Closure.LabelRed P host sL f n c bL sL' f' is'' ∧
      is' = vals us ++ is'' := Closure.Step.label_inv hs
  rw [he]
  cases hred with
  | ctxt h =>
    exact wrap_ctxt (.label n c) (.label n c') (.label n c') ih (sizeOf_label_body n c bL) hst
      hb h loose_label (.label n hc ·)
  | values vs => exact same_wrap (.label n c') hst hb.eq_vals Step.labelVals
  | brZero hl hn => exact label_brZero hst hc hb hl hn
  | brSucc hl => exact exit_wrap _ hst hb trivial (by simp) fun _ => Step.brLabelSucc hl
  | returnCallRef hr =>
    exact exit_wrap _ hst hb (flat_of_isReturnCallRef hr).1 (flat_of_isReturnCallRef hr).2
      fun _ => Step.returnCallRefLabel hr
  | return_ => exact exit_wrap _ hst hb trivial (by simp) fun _ => Step.returnLabel
  | throwRef a => exact same_wrap (.label n c') hst hb.eq_throwing Step.throwRefLabel
  | trap => exact same_wrap (.label n c') hst hb.eq_trap Step.trapLabel

/-- The bubbling rules of a `HANDLER`. -/
theorem handler_exit {n : Nat} {cs : List Catch} {sL sR : Store H} {f : Frame}
    {us vs : List Val} {k rest bR : List Admin} (hst : StoreRel FR sL sR)
    (hb : LRel (vals vs ++ k ++ rest) bR)
    (hk : (∃ l, k = [.plain (.br l)]) ∨ k = [.plain .return_] ∨
      ∃ c : Admin, c.IsReturnCallRef ∧ k = [c]) :
    Goal P host sL sR f f (vals us ++ [.handler n cs bR]) (vals us ++ (vals vs ++ k)) := by
  rcases hk with ⟨l, rfl⟩ | rfl | ⟨c, hc, rfl⟩
  · exact exit_wrap (.handler n cs) hst hb trivial (by simp) fun _ => Step.brHandler
  · exact exit_wrap (.handler n cs) hst hb trivial (by simp) fun _ => Step.returnHandler
  · exact exit_wrap (.handler n cs) hst hb (flat_of_isReturnCallRef hc).1
      (flat_of_isReturnCallRef hc).2 fun _ => Step.returnCallRefHandler hc

/-- A step at a `HANDLER` head with a related body. -/
theorem handler_case (hhost : HostRespects FR host) {n : Nat} {cs : List Catch}
    {bL bR : List Admin} (ih : SimIH P host (sizeOf (Admin.handler n cs bL)))
    {sL sL' sR : Store H} {f f' : Frame} {us : List Val} {is' : List Admin}
    (hst : StoreRel FR sL sR) (hb : LRel bL bR)
    (hs : Execution.Core.Step P host ⟨sL, f, vals us ++ [.handler n cs bL]⟩ ⟨sL', f', is'⟩) :
    Goal P host sL' sR f f' (vals us ++ [.handler n cs bR]) is' := by
  obtain ⟨is'', hinv, he⟩ : ∃ is'', HandlerInv P host sL f n cs bL sL' f' is'' ∧
      is' = vals us ++ is'' := Sim.Step.handler_inv hs
  rcases hinv with ⟨b', h, rfl⟩ | ⟨rfl, rfl, vs, rfl, rfl⟩ |
      ⟨rfl, rfl, vs, k, rest, hk, rfl, rfl⟩ | ⟨hk, -⟩
  · rw [he]
    exact wrap_ctxt (.handler n cs) (.handler n cs) (.handler n cs) ih
      (sizeOf_handler_body n cs bL) hst hb h loose_handler (.handler n cs ·)
  · rw [he]; exact same_wrap (.handler n cs) hst hb.eq_vals Step.handlerVals
  · rw [he]; exact handler_exit hst hb hk
  · have hbR : bR = bL := by rcases hk with rfl | ⟨a, rfl⟩ <;> first | exact hb.eq_trap |
      exact hb.eq_throwing
    rw [hbR]
    exact same_case hhost hst hs

/-- `return_call_ref-frame-addr`: the callee's type is read from the related store. -/
theorem frame_callAddr {n : Nat} {fi : Frame} {sL sR : Store H} {f : Frame} {us vs' vs : List Val}
    {a : Nat} {c : Admin} {rest bR : List Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)}
    (hst : StoreRel FR sL sR) (hb : LRel (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest) bR)
    (hc : c.IsReturnCallRef) (hfn : sL.funcs[a]? = some fn) (he : Expand fn.type (.func ps rs))
    (hn : vs.length = ps.length) :
    Goal P host sL sR f f (vals us ++ [.frame n fi bR])
      (vals us ++ (vals vs ++ [.ref (.func a), c.retToCallIn fi.module])) := by
  obtain ⟨fn', hfn', hty⟩ : ∃ fn', sR.funcs[a]? = some fn' ∧ fn'.type = fn.type :=
    hst.func_type hfn
  refine exit_wrap (vs := vs' ++ vs ++ [.ref (.func a)]) (k := c) (rest := rest) (.frame n fi)
    hst (by simpa [vals, Val.toAdmin] using hb) (flat_of_isReturnCallRef hc).1
    (flat_of_isReturnCallRef hc).2 fun R' => ?_
  simpa [vals, Val.toAdmin] using Step.returnCallRefFrameAddr (P := P) (host := host) (s := sR)
    (f := f) (fi := fi) (k := n) (vs' := vs') (vs := vs) (rest := R') hc hfn' (hty ▸ he) hn

/-- A step at a `FRAME` head with a related body. -/
theorem frame_case {n : Nat} {fi : Frame} {bL bR : List Admin}
    (ih : SimIH P host (sizeOf (Admin.frame n fi bL))) {sL sL' sR : Store H} {f f' : Frame}
    {us : List Val} {is' : List Admin} (hst : StoreRel FR sL sR) (hb : LRel bL bR)
    (hs : Execution.Core.Step P host ⟨sL, f, vals us ++ [.frame n fi bL]⟩ ⟨sL', f', is'⟩) :
    Goal P host sL' sR f f' (vals us ++ [.frame n fi bR]) is' := by
  obtain ⟨is₀, hcode, hred⟩ : ∃ is₀, is' = vals us ++ is₀ ∧
      Closure.FrameRedex P host sL f n fi bL sL' f' is₀ :=
    Closure.Step.frame_redex_aux hs us n fi bL rfl
  rw [hcode]
  cases hred with
  | @ctxt _ _ _ fi' _ _ _ h =>
    exact wrap_ctxt (.frame n fi') (.frame n fi) (.frame n fi') ih (sizeOf_frame_body n fi bL)
      hst hb h loose_frame (.frame n fi' ·)
  | values hn => exact same_wrap (.frame n fi) hst hb.eq_vals (Step.frameVals hn)
  | @ret _ _ _ vs' vs rest hn =>
    exact exit_wrap (vs := vs' ++ vs) (k := .plain .return_) (rest := rest) _ hst
      (by simpa using hb) trivial (by simp) fun R' => by
        simpa using Step.returnFrame (P := P) (host := host) (fi := fi) (vs' := vs') (vs := vs)
          (rest := R') hn
  | @callNull _ _ _ vs c rest hc =>
    exact exit_wrap (vs := vs ++ [.ref .null]) (k := c) (rest := rest) _ hst
      (by simpa [vals, Val.toAdmin] using hb) (flat_of_isReturnCallRef hc).1
      (flat_of_isReturnCallRef hc).2 fun R' => by
        simpa [vals, Val.toAdmin] using Step.returnCallRefFrameNull (P := P) (host := host)
          (fi := fi) (k := n) (vs := vs) (rest := R') hc
  | callAddr hc hfn he hn => exact frame_callAddr hst hb hc hfn he hn
  | throw => exact same_wrap (.frame n fi) hst hb.eq_throwing Step.throwRefFrame
  | trap => exact same_wrap (.frame n fi) hst hb.eq_trap Step.trapFrame

/-! ## Pointwise heads -/

/-- **A step at a pointwise head.** -/
theorem head_case (hhost : HostRespects FR host) {a b : Admin} (ih : SimIH P host (sizeOf a))
    {sL sL' sR : Store H} {f f' : Frame} {us : List Val} {is' : List Admin}
    (hst : StoreRel FR sL sR) (hab : ARel a b)
    (hs : Execution.Core.Step P host ⟨sL, f, vals us ++ [a]⟩ ⟨sL', f', is'⟩) :
    ∃ sR' isR, Loose.Step P host ⟨sR, f, vals us ++ [b]⟩ ⟨sR', f', isR⟩ ∧
      StoreRel FR sL' sR' ∧ LRel is' isR := by
  cases hab with
  | refl => exact same_case hhost hst hs
  | @plain i j hij =>
    by_cases hi : Closure.IsStructInstr i
    · obtain ⟨hs', r', hr, hstep⟩ := Closure.struct_match_aux (BI := fuseBI)
        (B := fun _ _ => False) hs us i j rfl hi hij
      dsimp only at hs' hr hstep
      subst hs'
      exact ⟨sR, r', core (hstep sR), hst, LRel.ofAdminsRel hr⟩
    · have hji : j = i := by
        cases hij with
        | refl => rfl
        | _ => exact (hi trivial).elim
      subst hji
      exact same_case hhost hst hs
  | label n hc hb => exact label_case ih hst hc hb hs
  | handler n cs hb => exact handler_case hhost ih hst hb hs
  | frame n fi hb => exact frame_case ih hst hb hs

/-! ## Kernel heads and translated patterns -/

/-- The redex results of a `trap` or `THROW_REF` head end in a kernel. -/
theorem kernel_shape {sL sL' : Store H} {f f' : Frame} {us : List Val} {k : Admin}
    {is' : List Admin} (hk : k = .trap ∨ k = .plain .throwRef)
    (hs : Execution.Core.Step P host ⟨sL, f, vals us ++ [k]⟩ ⟨sL', f', is'⟩) :
    ∃ Q k', (k' = .trap ∨ k' = .plain .throwRef) ∧ is' = vals Q ++ [k'] := by
  rcases hk with rfl | rfl
  · obtain ⟨-, -, p, -, q, -, -, he⟩ := Sim.Step.trap_redex_aux hs us rfl
    exact ⟨p ++ q, .trap, Or.inl rfl, he⟩
  · obtain ⟨-, -, ⟨p, -, q, a, -, -, he⟩ | ⟨-, u', -, he⟩⟩ :=
      Sim.Step.throwRef_redex_aux hs us rfl
    · dsimp only at he
      exact ⟨p ++ q ++ [.ref (.exn a)], .plain .throwRef, Or.inr rfl,
        by rw [he]; simp [vals, throwing, Val.toAdmin]⟩
    · exact ⟨u', .trap, Or.inl rfl, he⟩

/-- The redex of a `trap` or `THROW_REF` head: the same redex on the right. -/
theorem kernel_redex {sL sL' sR : Store H} {f f' : Frame} {ws us : List Val} {k : Admin}
    {es r is' : List Admin} (hst : StoreRel FR sL sR) (hk : k = .trap ∨ k = .plain .throwRef)
    (hlen : es.length = r.length)
    (hs : Execution.Core.Step P host ⟨sL, f, vals us ++ [k]⟩ ⟨sL', f', is'⟩) :
    Goal P host sL' sR f f' (vals (ws ++ us) ++ k :: r) (vals ws ++ is' ++ es) := by
  have hctx : ¬ k.IsCtx := by rcases hk with rfl | rfl <;> exact id
  have hcall : ¬ k.IsCallRef := by rcases hk with rfl | rfl <;> exact id
  obtain ⟨sR', hsR, hst'⟩ : ∃ sR', Execution.Core.Step P host ⟨sR, f, vals us ++ [k]⟩
      ⟨sR', f', is'⟩ ∧ StoreRel FR sL' sR' := Sim.Step.transport_storeRel hst hctx hcall hs
  obtain ⟨Q, k', hk', hQ⟩ : ∃ Q k', (k' = .trap ∨ k' = .plain .throwRef) ∧
      is' = vals Q ++ [k'] := kernel_shape hk hs
  have hl : Loose.Step P host ⟨sR, f, vals ws ++ (vals us ++ [k]) ++ r⟩
      ⟨sR', f', vals ws ++ is' ++ r⟩ := loose_ctx (core hsR) ws r
  have hr : LRel (vals (ws ++ Q) ++ k' :: es) (vals (ws ++ Q) ++ k' :: r) :=
    LRel.vals_append _ (LRel.cut hk' hlen)
  refine ⟨sR', _, by simpa using hl, hst', ?_⟩
  rw [hQ]; simpa using hr

theorem take_ne_nil {α : Type} {r₁ r₂ r : List α} (hlen : (r₁ ++ r₂).length = r.length)
    (hne : r₁ ≠ []) : r.take r₁.length ≠ [] := by
  intro h0
  have hl : (r.take r₁.length).length = r₁.length := by
    rw [List.length_take]; simp only [List.length_append] at hlen; omega
  rw [h0] at hl
  exact hne (List.length_eq_zero_iff.mp hl.symm)

/-- `trap-instrs`: the right side discards as many instructions. -/
theorem kernel_trap {sL sR : Store H} {f : Frame} {ws us : List Val} {r₁ r₂ r : List Admin}
    (hst : StoreRel FR sL sR) (hlen : (r₁ ++ r₂).length = r.length) (hne : us ≠ [] ∨ r₁ ≠ []) :
    Goal P host sL sR f f (vals (ws ++ us) ++ .trap :: r) (vals ws ++ [.trap] ++ r₂) := by
  have hne' : us ≠ [] ∨ r.take r₁.length ≠ [] := hne.imp id (take_ne_nil hlen)
  have hs : Execution.Core.Step P host ⟨sR, f, vals us ++ [.trap] ++ r.take r₁.length⟩
      ⟨sR, f, [.trap]⟩ := Step.trapInstrs hne'
  have hcode : vals (ws ++ us) ++ .trap :: r =
      vals ws ++ (vals us ++ [.trap] ++ r.take r₁.length) ++ r.drop r₁.length := by
    conv_lhs => rw [← List.take_append_drop r₁.length r]
    simp
  have hdrop : r₂.length = (r.drop r₁.length).length := by
    simp only [List.length_append] at hlen; simp only [List.length_drop]; omega
  have hr : LRel (vals ws ++ .trap :: r₂) (vals ws ++ .trap :: r.drop r₁.length) :=
    LRel.vals_append ws (LRel.cut (Or.inl rfl) hdrop)
  refine ⟨sR, vals ws ++ [.trap] ++ r.drop r₁.length, ?_, hst, by simpa using hr⟩
  rw [hcode]; exact loose_ctx (core hs) ws _

/-- `throw_ref-instrs`: the right side discards as many instructions. -/
theorem kernel_throw {sL sR : Store H} {f : Frame} {ws us : List Val} {x : Nat}
    {r₁ r₂ r : List Admin} (hst : StoreRel FR sL sR) (hlen : (r₁ ++ r₂).length = r.length)
    (hne : us ≠ [] ∨ r₁ ≠ []) :
    Goal P host sL sR f f (vals (ws ++ us ++ [.ref (.exn x)]) ++ .plain .throwRef :: r)
      (vals ws ++ throwing x ++ r₂) := by
  have hne' : us ≠ [] ∨ r.take r₁.length ≠ [] := hne.imp id (take_ne_nil hlen)
  have hs : Execution.Core.Step P host ⟨sR, f, vals us ++ throwing x ++ r.take r₁.length⟩
      ⟨sR, f, throwing x⟩ := Step.throwRefInstrs hne'
  have hcode : vals (ws ++ us ++ [.ref (.exn x)]) ++ .plain .throwRef :: r =
      vals ws ++ (vals us ++ throwing x ++ r.take r₁.length) ++ r.drop r₁.length := by
    conv_lhs => rw [← List.take_append_drop r₁.length r]
    simp [vals, throwing, Val.toAdmin]
  have hdrop : r₂.length = (r.drop r₁.length).length := by
    simp only [List.length_append] at hlen; simp only [List.length_drop]; omega
  have hr : LRel (vals (ws ++ [.ref (.exn x)]) ++ .plain .throwRef :: r₂)
      (vals (ws ++ [.ref (.exn x)]) ++ .plain .throwRef :: r.drop r₁.length) :=
    LRel.vals_append _ (LRel.cut (Or.inr rfl) hdrop)
  refine ⟨sR, vals ws ++ throwing x ++ r.drop r₁.length, ?_, hst,
    by simpa [vals, throwing, Val.toAdmin] using hr⟩
  rw [hcode]; exact loose_ctx (core hs) ws _

/-- **A `trap` or `THROW_REF` head.** -/
theorem kernel_case {sL sL' sR : Store H} {f f' : Frame} {V : List Val} {k : Admin}
    {es r wL' : List Admin} (hst : StoreRel FR sL sR) (hk : k = .trap ∨ k = .plain .throwRef)
    (hlen : es.length = r.length)
    (h : Execution.Core.Step P host ⟨sL, f, vals V ++ k :: es⟩ ⟨sL', f', wL'⟩) :
    Goal P host sL' sR f f' (vals V ++ k :: r) wL' := by
  have hka : k.val? = none := by rcases hk with rfl | rfl <;> rfl
  rcases Sim.Step.split_head hka h with ⟨ws, us, is', rfl, hs, rfl⟩ |
      ⟨rfl, rfl, rfl, ws, us, r₁, r₂, rfl, rfl, hne, rfl⟩ |
      ⟨rfl, rfl, rfl, ws, us, x, r₁, r₂, rfl, rfl, hne, rfl⟩
  · exact kernel_redex hst hk hlen hs
  · exact kernel_trap hst hlen hne
  · exact kernel_throw hst hlen hne

/-- **A translated pattern**: the left reads the local, the right takes `selectEither`. -/
theorem group_case {sL sL' sR : Store H} {f f' : Frame} {V : List Val} {x : LocalIdx}
    {t : Option (List ValType)} {l r wL' : List Admin} (hst : StoreRel FR sL sR) (hl : LRel l r)
    (h : Execution.Core.Step P host
      ⟨sL, f, vals V ++ .plain (.localGet x) ::
        ([.plain .drop, .plain (.intConst .i32 0), .plain (.select t)] ++ l)⟩ ⟨sL', f', wL'⟩) :
    ∃ sR' R', Loose.Step P host ⟨sR, f, vals V ++ (expression (zeroTestSel x t) ++ r)⟩
      ⟨sR', f', R'⟩ ∧ StoreRel FR sL' sR' ∧ LRel wL' R' := by
  rcases Sim.Step.split_head rfl h with ⟨ws, us, is', rfl, hs, rfl⟩ | ⟨hk, -⟩ | ⟨hk, -⟩
  · obtain ⟨rfl, rfl, v, hv, rfl⟩ := Step.localGet_inv hs
    have hq : Loose.Quirk ⟨sR, f', expression (zeroTestSel x t)⟩
        ⟨sR, f', [v.toAdmin, .plain .drop, .plain (.intConst .i32 0), .plain (.select t)]⟩ :=
      Loose.Quirk.selectEither false hv
    refine ⟨sR, vals (ws ++ us) ++ [v.toAdmin, .plain .drop, .plain (.intConst .i32 0),
      .plain (.select t)] ++ r, ?_, hst, ?_⟩
    · have := Ctx.instrs (vs := ws ++ us) (rest := r) (Ctx.base hq)
      exact Or.inr (by simpa using this)
    · have := LRel.vals_append (ws ++ us)
        ((LRel.refl [v.toAdmin, .plain .drop, .plain (.intConst .i32 0), .plain (.select t)]).append
          hl)
      simpa using this
  · cases hk
  · cases hk

/-! ## The simulation -/

/-- A pointwise head that is not a kernel. -/
theorem pointwise_case (hhost : HostRespects FR host) {m : Nat}
    (ihm : ∀ k < m, SimIH P host k) {sL sL' sR : Store H} {f f' : Frame} {V : List Val}
    {a b : Admin} {es r wL' : List Admin} (hm : sizeOf (vals V ++ a :: es) < m)
    (ha : a.val? = none) (hk : ¬ (a = .trap ∨ a = .plain .throwRef)) (hst : StoreRel FR sL sR)
    (hab : ARel a b) (hl : LRel es r)
    (h : Execution.Core.Step P host ⟨sL, f, vals V ++ a :: es⟩ ⟨sL', f', wL'⟩) :
    Goal P host sL' sR f f' (vals V ++ b :: r) wL' := by
  rcases Sim.Step.split_head ha h with ⟨ws, us, is', rfl, hs, rfl⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · have hlt : sizeOf a < m :=
      Nat.lt_trans (List.sizeOf_lt_of_mem (by simp : a ∈ vals (ws ++ us) ++ a :: es)) hm
    obtain ⟨sR', isR, hstep, hst', hrel⟩ := head_case hhost (ihm _ hlt) hst hab hs
    have hl' : Loose.Step P host ⟨sR, f, vals ws ++ (vals us ++ [b]) ++ r⟩
        ⟨sR', f', vals ws ++ isR ++ r⟩ := loose_ctx hstep ws r
    exact ⟨sR', _, by simpa using hl', hst', (LRel.vals_append ws hrel).append hl⟩
  · exact absurd (Or.inl rfl) hk
  · exact absurd (Or.inr rfl) hk

/-- **The one-step simulation**, by strong induction on the size of the left code. -/
theorem sim_main (hhost : HostRespects FR host) : ∀ m, SimIH P host m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro sL sL' sR f f' wL wL' R hm h hst hw
  obtain ⟨V, a, es, ha, rfl⟩ := exists_head_of_not_all h.not_all_isVal
  obtain ⟨R₀, rfl, h₀⟩ := LRel.peel V hw
  by_cases hk : a = .trap ∨ a = .plain .throwRef
  · obtain ⟨r, rfl, hlen⟩ := h₀.kernel_inv hk
    exact kernel_case hst hk hlen h
  · rcases h₀.cons_inv with ⟨b, r, rfl, hab, hl⟩ | ⟨x, t, l, r, rfl, rfl, rfl, hl⟩ |
        ⟨hk', -⟩
    · exact pointwise_case hhost ihm hm ha hk hst hab hl h
    · exact group_case hst hl h
    · exact absurd hk' hk

/-! ## Behaviours -/

/-- The simulation relation on configurations. -/
def SimR (c d : Config H) : Prop :=
  c.frame = d.frame ∧ StoreRel FR c.store d.store ∧ LRel c.code d.code

/-- **wasmi's behaviours are loose behaviours**: every Core behaviour of an invocation of the
translated store is a loose behaviour of the same invocation of the source store. -/
theorem behaviours_subset (hhost : HostRespects FR host) (s : Store H) (a : Nat)
    (vs : List Val) :
    behaviours P host (fuseStore s) a vs ⊆ behavioursR (Loose.Step P host) (invoke s a vs) := by
  refine behavioursR_subset_of_sim (Rel := SimR) ?_ ?_ ?_
  · intro c c' d hs hr
    obtain ⟨sL, f, wL⟩ := c
    obtain ⟨sL', f', wL'⟩ := c'
    obtain ⟨sR, g, R⟩ := d
    obtain ⟨hfg, hst, hw⟩ := hr
    dsimp only at hfg hst hw
    subst hfg
    obtain ⟨sR', R', hl, hst', hr'⟩ := sim_main hhost _ (Nat.lt_succ_self _) hs hst hw
    exact ⟨⟨sR', f', R'⟩, hl, rfl, hst', hr'⟩
  · intro c d r hr hc
    have h := hr.2.2
    rw [hc] at h
    exact h.result_inv
  · refine ⟨?_, ?_, ?_⟩
    · rw [invoke_fuseStore]
    · rw [invoke_fuseStore]; exact storeRel_fuseStore s
    · rw [invoke_fuseStore]; exact LRel.refl _

end Silmaril.Proofs.Wasm.Wasmi
