module

public import Silmaril.Proofs.Wasm.Wasmi.LooseW.Rel
public import Silmaril.Wasm.Wasmi.Thms
public import Silmaril.Wasm.Atlas.Variant.Thms
public import Silmaril.Wasm.Execution.Core.Sim.StepMatch
public import Silmaril.Wasm.Execution.Core.Sim.Segments
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Label
public import Silmaril.Wasm.Execution.Core.Sim.Closure.HandlerInv
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Frame
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Struct

@[expose] public section

/-!
# `fuseW`'s translated code against `LooseW`: pointwise and context heads

The simulation of `Silmaril.Proofs.Wasm.Wasmi.Sim`, made stuttering. A left (Core, translated
store) step is matched by a `LooseW` step from the related right code, **or by no step**, in
which case the size of the left code decreases (`Goal`). Stuttering arises only after a `trap`
or `THROW_REF` (`Silmaril.Proofs.Wasm.Wasmi.LooseW.Sim`); this file lifts both kinds of match
through value prefixes, code suffixes, `LABEL`, `HANDLER` and `FRAME`:

* `sizeOf_mid`: replacing a smaller middle part makes a smaller code;
* `wrap_ctxt`: an inner match under a context, by the induction hypothesis;
* `label_case`, `handler_case`, `frame_case`, `head_case`: as in the lock-step proof, with the
  bubbling rules matched by the same rule on the right.

New proofs, using silmaril-lean's code-relation kit (`Silmaril/Wasm/Execution/Core/Sim/*`) and
the `local.get` inversion of `Silmaril.Proofs.Wasm.Wasmi` (through its header).
-/

namespace Silmaril.Proofs.Wasm.Wasmi.LooseW

open Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (Ty Expand)
open Silmaril.Wasm.Wasmi Silmaril.Wasm.Wasmi.LooseW Silmaril.Wasm.Atlas.Variant

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The function relation of the wider translation. -/
abbrev FR : FuncInst H → FuncInst H → Prop := FuncRel fuseWBI

/-- **The conclusion of a matched step**: a `LooseW` step from the right code `R`, or no step
with a smaller left code; related stores and related results. -/
def Goal (P : Profile) (host : HostSemantics H) (sL' sR : Store H) (f f' : Frame)
    (R wL wL' : List Admin) : Prop :=
  ∃ sR' R', (LooseW.Step P host ⟨sR, f, R⟩ ⟨sR', f', R'⟩ ∨
      (sR' = sR ∧ f' = f ∧ R' = R ∧ sizeOf wL' < sizeOf wL)) ∧
    StoreRel FR sL' sR' ∧ LRel wL' R'

/-- The simulation obligation for left code of size below `m`. -/
def SimIH (P : Profile) (host : HostSemantics H) (m : Nat) : Prop :=
  ∀ {sL sL' sR : Store H} {f f' : Frame} {wL wL' R : List Admin}, sizeOf wL < m →
    Execution.Core.Step P host ⟨sL, f, wL⟩ ⟨sL', f', wL'⟩ → StoreRel FR sL sR → LRel wL R →
    Goal P host sL' sR f f' R wL wL'

/-! ## Sizes -/

theorem sizeOf_append (X B : List Admin) : sizeOf (X ++ B) + 1 = sizeOf X + sizeOf B := by
  induction X with
  | nil => simp only [List.nil_append, List.nil.sizeOf_spec]; omega
  | cons x X ih => simp only [List.cons_append, List.cons.sizeOf_spec]; omega

/-- **Replacing a smaller middle part makes a smaller code.** -/
theorem sizeOf_mid (A B : List Admin) {X Y : List Admin} (h : sizeOf X < sizeOf Y) :
    sizeOf (A ++ X ++ B) < sizeOf (A ++ Y ++ B) := by
  have h₁ := sizeOf_append (A ++ X) B
  have h₂ := sizeOf_append (A ++ Y) B
  have h₃ := sizeOf_append A X
  have h₄ := sizeOf_append A Y
  omega

theorem sizeOf_single {a b : Admin} (h : sizeOf a < sizeOf b) : sizeOf [a] < sizeOf [b] := by
  simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec]; omega

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
theorem core {c c' : Config H} (h : Execution.Core.Step P host c c') : LooseW.Step P host c c' :=
  Or.inl h

/-- A matched step that is a Core step on the right. -/
theorem goal_core {sL' sR sR' : Store H} {f f' : Frame} {R wL wL' R' : List Admin}
    (h : Execution.Core.Step P host ⟨sR, f, R⟩ ⟨sR', f', R'⟩) (hst : StoreRel FR sL' sR')
    (hr : LRel wL' R') : Goal P host sL' sR f f' R wL wL' :=
  ⟨sR', R', Or.inl (core h), hst, hr⟩

/-- A related step on the same code, by silmaril-lean's `Step.match_storeRel`. -/
theorem same_case (hhost : HostRespects FR host) {sL sL' sR : Store H} {f f' : Frame}
    {w w' wL : List Admin} (hst : StoreRel FR sL sR)
    (hs : Execution.Core.Step P host ⟨sL, f, w⟩ ⟨sL', f', w'⟩) :
    Goal P host sL' sR f f' w wL w' := by
  obtain ⟨t', es'', ht, hst', hrel⟩ :=
    Sim.Step.match_storeRel (B := fun _ _ => False) (fun _ _ h => h) hhost hs sR hst
  exact goal_core ht hst' (LRel.ofAdminsRel hrel)

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

/-- An inner match under a context, by the induction hypothesis. On a stutter the inner frame
is unchanged, and `hstut` gives the outer frame, the right wrapper and the smaller left
code. -/
theorem wrap_ctxt (a : Admin) (wrapL' wrapR wrapR' : List Admin → Admin) {m : Nat}
    (ih : SimIH P host m) {sL sL' sR : Store H} {f₀ f₀' : Frame} {us : List Val}
    {bL bL' bR : List Admin} {g g' : Frame} (hlt : sizeOf bL < m) (hst : StoreRel FR sL sR)
    (hb : LRel bL bR) (h : Execution.Core.Step P host ⟨sL, g, bL⟩ ⟨sL', g', bL'⟩)
    (hwrap : ∀ {s s' R R'}, LooseW.Step P host ⟨s, g, R⟩ ⟨s', g', R'⟩ →
      LooseW.Step P host ⟨s, f₀, [wrapR R]⟩ ⟨s', f₀', [wrapR' R']⟩)
    (hrel : ∀ {R'}, LRel bL' R' → ARel (wrapL' bL') (wrapR' R'))
    (hstut : g' = g → sizeOf bL' < sizeOf bL →
      f₀' = f₀ ∧ wrapR' bR = wrapR bR ∧ sizeOf (wrapL' bL') < sizeOf a) :
    Goal P host sL' sR f₀ f₀' (vals us ++ [wrapR bR]) (vals us ++ [a])
      (vals us ++ [wrapL' bL']) := by
  obtain ⟨sR', bR', hl | ⟨rfl, rfl, rfl, hlt'⟩, hst', hr⟩ := ih hlt h hst hb
  · exact ⟨sR', _, Or.inl (loose_vals_left (hwrap hl) us), hst',
      LRel.vals_append us (.cons (hrel hr) .nil)⟩
  · obtain ⟨hf, hw, hsz⟩ := hstut rfl hlt'
    refine ⟨sR', _, Or.inr ⟨rfl, hf, by rw [hw], ?_⟩, hst',
      LRel.vals_append us (.cons (hrel hr) .nil)⟩
    simpa using sizeOf_mid (vals us) [] (sizeOf_single hsz)

/-- A bubbling rule at an exit shape `val* k rest` of the body: the same rule on the right. -/
theorem exit_wrap (wrap : List Admin → Admin) {sL sR : Store H} {f : Frame} {us vs : List Val}
    {k : Admin} {rest bR out wL : List Admin} (hst : StoreRel FR sL sR)
    (hb : LRel (vals vs ++ [k] ++ rest) bR) (hk : Flat k) (hl : ∀ x, k ≠ .plain (.localGet x))
    (hstep : ∀ R', Execution.Core.Step P host ⟨sR, f, [wrap (vals vs ++ [k] ++ R')]⟩ ⟨sR, f, out⟩) :
    Goal P host sL sR f f (vals us ++ [wrap bR]) wL (vals us ++ out) := by
  obtain ⟨R', hR'⟩ : ∃ R', bR = vals vs ++ [k] ++ R' := exit_inv hb hk hl
  rw [hR']
  exact goal_core (Sim.Step.vals_left (hstep R') us) hst (LRel.refl _)

/-- A bubbling rule at a body related only to itself (values, a trap, a thrown exception). -/
theorem same_wrap (wrap : List Admin → Admin) {sL sR : Store H} {f : Frame} {us : List Val}
    {bL bR out wL : List Admin} (hst : StoreRel FR sL sR) (hb : bR = bL)
    (hstep : Execution.Core.Step P host ⟨sR, f, [wrap bL]⟩ ⟨sR, f, out⟩) :
    Goal P host sL sR f f (vals us ++ [wrap bR]) wL (vals us ++ out) := by
  rw [hb]
  exact goal_core (Sim.Step.vals_left hstep us) hst (LRel.refl _)

/-- `br-label-zero`: the right side continues with its own (related) continuation. -/
theorem label_brZero {sL sR : Store H} {f : Frame} {us vs' vs : List Val} {n : Nat}
    {c c' : List Instr} {l : LabelIdx} {rest bR wL : List Admin} (hst : StoreRel FR sL sR)
    (hc : InstrsRel fuseWBI c c')
    (hb : LRel (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest) bR)
    (hl : l.toNat = 0) (hn : vs.length = n) :
    Goal P host sL sR f f (vals us ++ [.label n c' bR]) wL
      (vals us ++ (vals vs ++ expression c)) := by
  obtain ⟨R', hR'⟩ : ∃ R', bR = vals (vs' ++ vs) ++ [.plain (.br l)] ++ R' :=
    exit_inv (k := .plain (.br l)) (by simpa using hb) trivial (fun _ => by simp)
  have hs' : Execution.Core.Step P host ⟨sR, f, [.label n c' bR]⟩
      ⟨sR, f, vals vs ++ expression c'⟩ := by
    rw [hR']; simpa using Step.brLabelZero (P := P) (host := host) (s := sR) (f := f)
      (cont := c') (vs' := vs') (vs := vs) (rest := R') hl hn
  exact goal_core (Sim.Step.vals_left hs' us) hst
    (LRel.vals_append us (LRel.vals_append vs (LRel.src hc)))

/-- A step at a `LABEL` head with related continuation and body. -/
theorem label_case {n : Nat} {c c' : List Instr} {bL bR : List Admin}
    (ih : SimIH P host (sizeOf (Admin.label n c bL))) {sL sL' sR : Store H} {f f' : Frame}
    {us : List Val} {is' : List Admin} (hst : StoreRel FR sL sR) (hc : InstrsRel fuseWBI c c')
    (hb : LRel bL bR)
    (hs : Execution.Core.Step P host ⟨sL, f, vals us ++ [.label n c bL]⟩ ⟨sL', f', is'⟩) :
    Goal P host sL' sR f f' (vals us ++ [.label n c' bR]) (vals us ++ [.label n c bL]) is' := by
  obtain ⟨is'', hred, he⟩ : ∃ is'', Closure.LabelRed P host sL f n c bL sL' f' is'' ∧
      is' = vals us ++ is'' := Closure.Step.label_inv hs
  rw [he]
  cases hred with
  | ctxt h =>
    exact wrap_ctxt _ (.label n c) (.label n c') (.label n c') ih (sizeOf_label_body n c bL) hst
      hb h loose_label (.label n hc ·) fun hg hlt => ⟨hg, rfl, by
        simp only [Admin.label.sizeOf_spec]; omega⟩
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
    {us vs : List Val} {k rest bR wL : List Admin} (hst : StoreRel FR sL sR)
    (hb : LRel (vals vs ++ k ++ rest) bR)
    (hk : (∃ l, k = [.plain (.br l)]) ∨ k = [.plain .return_] ∨
      ∃ c : Admin, c.IsReturnCallRef ∧ k = [c]) :
    Goal P host sL sR f f (vals us ++ [.handler n cs bR]) wL (vals us ++ (vals vs ++ k)) := by
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
    Goal P host sL' sR f f' (vals us ++ [.handler n cs bR]) (vals us ++ [.handler n cs bL])
      is' := by
  obtain ⟨is'', hinv, he⟩ : ∃ is'', HandlerInv P host sL f n cs bL sL' f' is'' ∧
      is' = vals us ++ is'' := Sim.Step.handler_inv hs
  rcases hinv with ⟨b', h, rfl⟩ | ⟨rfl, rfl, vs, rfl, rfl⟩ |
      ⟨rfl, rfl, vs, k, rest, hk, rfl, rfl⟩ | ⟨hk, -⟩
  · rw [he]
    exact wrap_ctxt _ (.handler n cs) (.handler n cs) (.handler n cs) ih
      (sizeOf_handler_body n cs bL) hst hb h loose_handler (.handler n cs ·)
      fun hg hlt => ⟨hg, rfl, by simp only [Admin.handler.sizeOf_spec]; omega⟩
  · rw [he]; exact same_wrap (.handler n cs) hst hb.eq_vals Step.handlerVals
  · rw [he]; exact handler_exit hst hb hk
  · have hbR : bR = bL := by rcases hk with rfl | ⟨a, rfl⟩ <;> first | exact hb.eq_trap |
      exact hb.eq_throwing
    rw [hbR]
    exact same_case hhost hst hs

/-- `return_call_ref-frame-addr`: the callee's type is read from the related store. -/
theorem frame_callAddr {n : Nat} {fi : Frame} {sL sR : Store H} {f : Frame} {us vs' vs : List Val}
    {a : Nat} {c : Admin} {rest bR wL : List Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)}
    (hst : StoreRel FR sL sR) (hb : LRel (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest) bR)
    (hc : c.IsReturnCallRef) (hfn : sL.funcs[a]? = some fn) (he : Expand fn.type (.func ps rs))
    (hn : vs.length = ps.length) :
    Goal P host sL sR f f (vals us ++ [.frame n fi bR]) wL
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
    Goal P host sL' sR f f' (vals us ++ [.frame n fi bR]) (vals us ++ [.frame n fi bL]) is' := by
  obtain ⟨is₀, hcode, hred⟩ : ∃ is₀, is' = vals us ++ is₀ ∧
      Closure.FrameRedex P host sL f n fi bL sL' f' is₀ :=
    Closure.Step.frame_redex_aux hs us n fi bL rfl
  rw [hcode]
  cases hred with
  | @ctxt _ _ _ fi' _ _ _ h =>
    exact wrap_ctxt _ (.frame n fi') (.frame n fi) (.frame n fi') ih (sizeOf_frame_body n fi bL)
      hst hb h loose_frame (.frame n fi' ·) fun hg hlt => by
        subst hg; exact ⟨rfl, rfl, by simp only [Admin.frame.sizeOf_spec]; omega⟩
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
    Goal P host sL' sR f f' (vals us ++ [b]) (vals us ++ [a]) is' := by
  cases hab with
  | refl => exact same_case hhost hst hs
  | @plain i j hij =>
    by_cases hi : Closure.IsStructInstr i
    · obtain ⟨hs', r', hr, hstep⟩ := Closure.struct_match_aux (BI := fuseWBI)
        (B := fun _ _ => False) hs us i j rfl hi hij
      dsimp only at hs' hr hstep
      subst hs'
      exact goal_core (hstep sR) hst (LRel.ofAdminsRel hr)
    · have hji : j = i := by
        cases hij with
        | refl => rfl
        | _ => exact (hi trivial).elim
      subst hji
      exact same_case hhost hst hs
  | label n hc hb => exact label_case ih hst hc hb hs
  | handler n cs hb => exact handler_case hhost ih hst hb hs
  | frame n fi hb => exact frame_case ih hst hb hs

end Silmaril.Proofs.Wasm.Wasmi.LooseW
