module

public import Silmaril.Wasm.Resource.OBClient.Defs
public import Silmaril.Wasm.Resource.Client.Thms
public import Silmaril.Wasm.Logic.Hoare.Thms

/-!
# The borrowing-client analysis: every play is accepted by the ownership protocol

`OBIn I G R fs ia iu ρ` collects what the checker establishes: the thread-level client analysis
(`ClientCore`, with the held handles as the live list, no global pairs and no free import), the
role exports `R` (entered only by the environment, bodies checked from `loc 0`), and the roles.

* `EntryO`: a pending invocation of a role export whose argument is held; its only step enters
  the callee frame (`Silmaril.Wasm.Logic.Hoare.call_step_inv`), where the entry fact holds
  (`invC_entry`).
* `JO`: **the protocol invariant of `I.dlts P I.store`** for `(obSpec ρ).comap moveEvent`; an
  invariant, guarded or entering thread, with the held list of the protocol state.
* `obIn_sound`: the ownership sentence over `wasmSem P`, every profile; `checkOB_sound`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource.OBClient

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Resource Silmaril.Wasm.Resource.Client
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Verify (CfgIn CodeIn FrameIn StoreIn RefIn FuncsClosed CallPl Avoids isHost PlOK
  invoke_cfgIn typed_refIn answer_refIn callout_mem decompose_toAdmin_none ifaceOp?_fst ifaceOp?_snd
  isHost_iff refFuncs)

/-! ## Protocol facts -/

/-- The held handles of an ownership state. -/
def heldL (L : List (Val × Mode)) : List Val := L.map Prod.fst

theorem held_iff (L : List (Val × Mode)) (h : Val) : held L h = true ↔ h ∈ heldL L := by
  simp [held, heldL]

section
variable {X : WIface}

/-- Environment moves never break the ownership sentence. -/
theorem obSpec_oTotal (ρ : OBRoles X) :
    OTotal ((obSpec ρ).comap
      (moveEvent : Move (ifaceSig X.imports) (ifaceSig X.exports) → WEvent X)) := by
  intro q o ho
  rcases q with _ | L
  · rfl
  rcases o with (e | ⟨e, w⟩) | (⟨j, a⟩ | ⟨f, w⟩)
  · exact ho.elim
  · show (obStep (some L) (obEv ρ (.inl (evOf (.ans e w))))).isSome
    simp only [evOf, obEv]
    split
    · cases Answer.toBehaviour w with
      | returns vs =>
        rcases vs with _ | ⟨h, _ | _⟩ <;> simp only [OEv.ofRes, obStep] <;> (try split) <;> rfl
      | _ => rfl
    · rfl
  · show (obStep (some L) (obEv ρ (.inr (evOf (.ask ⟨j, a⟩))))).isSome
    simp only [evOf, obEv]
    split
    · rcases a.1 with _ | ⟨h, _ | _⟩ <;> simp only [OEv.ofArgs, obStep] <;> (try split) <;> rfl
    · split
      · rcases a.1 with _ | ⟨h, _ | _⟩ <;> simp only [OEv.ofArgs, obStep] <;> (try split) <;> rfl
      · rfl
  · exact ho.elim

end

/-! ## What the checker establishes -/

/-- The free import of the analysis is no import of the instance. -/
theorem noImp_host_false {I : ScalarInstance} (hok : I.Ok) {s : Store Nat}
    (hs : s.funcs = I.store.funcs) (b : Nat) : isHost s (noImp I) b = false := by
  cases hh : isHost s (noImp I) b
  · rfl
  · obtain ⟨fi, hfi, hhost⟩ := isHost_iff.1 hh
    obtain ⟨hlt, -⟩ := hok.host_type b fi _ (hs ▸ hfi) hhost
    exact absurd hlt (Nat.lt_irrefl _)

/-- **What the borrowing-client checker establishes.** -/
structure OBIn (I : ScalarInstance) (G R : Nat → Prop) (fs : List Nat) (ia iu : Nat)
    (ρ : OBRoles (ifaceOf I)) : Prop where
  core : ClientCore I G fs ia iu (noImp I) []
  ent : ∀ a, R a → ∃ (fi : FuncInst Nat) (code : Func), I.store.funcs[a]? = some fi ∧
    fi.code = .wasm code ∧ fi.module.funcs = fs ∧
    (∀ i ∈ code.body, PlOK (CallPl G (isBadC I.store ia iu (noImp I)) fs) i) ∧
    okL (cfgOf I.store fs ia iu (noImp I) []) fi.module.globals [.loc 0] .other code.body = true
  role : ∀ j, (ρ.lend j || ρ.take j) = true → R (I.addr j) ∧ (I.exports.get j).params.length = 1
  plain : ∀ j, (ρ.lend j || ρ.take j) = false → G (I.addr j)
  alloc : ∀ i : (ifaceOf I).Imp, ρ.alloc i = (i.val == ia)
  use : ∀ i : (ifaceOf I).Imp, ρ.use i = (i.val == iu)
  drop : ∀ i : (ifaceOf I).Imp, (ρ.free i || ρ.give i) = true → Avoids G I.store.funcs i.val

section
variable {I : ScalarInstance} {G R : Nat → Prop} {fs : List Nat} {ia iu : Nat}
  {ρ : OBRoles (ifaceOf I)}

/-- The thread-level invariant of the client analysis, for the borrowing client. -/
abbrev InvO (I : ScalarInstance) (G : Nat → Prop) (fs : List Nat) (ia iu : Nat) :=
  InvC I G fs ia iu (noImp I) []

/-- The guarded threads of the client analysis, for the borrowing client. -/
abbrev GuardedO (I : ScalarInstance) (G : Nat → Prop) (fs : List Nat) (ia iu : Nat) :=
  GuardedC I G fs ia iu (noImp I) []

/-- **A pending invocation of a role export** whose argument is held. -/
def EntryO (I : ScalarInstance) (G R : Nat → Prop) (fs : List Nat) (ia iu : Nat)
    (Lh : List Val) (s : Store Nat) (t : Thread) : Prop :=
  ∃ (a : Nat) (h : Val) (fi : FuncInst Nat) (code : Func) (ps rs : Ty (.list .val)),
    t = .pending a [h] ∧ R a ∧ h ∈ Lh ∧ StoreIn G s ∧ (∀ r, Val.ref r ∈ [h] → RefIn G r) ∧
    s.funcs[a]? = some fi ∧ fi.code = .wasm code ∧ Expand fi.type (.func ps rs) ∧
    [h].length = ps.length ∧ fi.module.funcs = fs ∧
    (∀ i ∈ code.body, PlOK (CallPl G (isBadC I.store ia iu (noImp I)) fs) i) ∧
    okL (cfgOf I.store fs ia iu (noImp I) []) fi.module.globals [.loc 0] .other code.body = true

/-- The entered callee frame of a role export is invariant: its parameter is held. -/
theorem invC_entry {Lh : List Val} {s : Store Nat} {h : Val} {fi : FuncInst Nat} {code : Func}
    {rs : Ty (.list .val)} (hs : StoreIn G s) (hh : h ∈ Lh)
    (hr : ∀ r, Val.ref r ∈ [h] → RefIn G r) (hm : fi.module.funcs = fs)
    (hpl : ∀ i ∈ code.body, PlOK (CallPl G (isBadC I.store ia iu (noImp I)) fs) i)
    (hok : okL (cfgOf I.store fs ia iu (noImp I) []) fi.module.globals [.loc 0] .other code.body
      = true) :
    InvO I G fs ia iu Lh ⟨s, {}, [Silmaril.Wasm.Logic.Hoare.callFrame fi code rs [h]]⟩ := by
  have hfr : FrameIn G fs (Frame.forCall fi.module [h] code.locals) :=
    Silmaril.Wasm.Verify.FrameIn.forCall hm hr _
  have hcode : CodeIn G fs (CallPl G (isBadC I.store ia iu (noImp I)) fs)
      [Silmaril.Wasm.Logic.Hoare.callFrame fi code rs [h]] :=
    CodeIn.frame_iff.2 ⟨hfr, CodeIn.label_iff.2 ⟨by simp, CodeIn.expression hpl⟩⟩
  have hsound : SoundF [] Lh s.globals (Frame.forCall fi.module [h] code.locals).locals [.loc 0] := by
    intro f hf
    simp only [List.mem_singleton] at hf
    subst hf
    exact ⟨h, by simp [Frame.forCall], hh, fun p hp => by cases hp⟩
  have hbody := okA_body (L := Lh) (gl := s.globals)
    (lc := (Frame.forCall fi.module [h] code.locals).locals) hok .other []
  simp only [vals, List.map_nil, List.nil_append] at hbody
  have h0 : FrameIn G fs ({} : Frame) := ⟨.inr rfl, fun r hr => by simp at hr⟩
  have hsig : Client.Sigma [] Lh s.globals := fun p hp => by simp at hp
  refine ⟨⟨hs, h0, hcode⟩, hsig, [], SoundF_nil, ?_⟩
  show okA _ Lh s.globals ({} : Frame).module.globals ({} : Frame).locals ⟨[], .other, true⟩
    [.frame rs.length (Frame.forCall fi.module [h] code.locals)
      [.label rs.length [] (expression code.body)]]
  rw [okA_frame_pre other_ne_ex]
  refine ⟨okX_frame.2 ⟨[.loc 0], hsound, ?_⟩, trivial⟩
  rw [okA_label_pre other_ne_ex]
  exact ⟨okX_label.2 ⟨rfl, [.loc 0], hsound, hbody⟩, trivial⟩

/-- The code of a pending invocation is not a result. -/
theorem invoke_ne_result {s : Store Nat} {a : Nat} {vs : List Val} (r : Result) :
    (invoke s a vs).code ≠ r.toAdmin := by
  intro hc
  have hl : (invoke s a vs).code.getLast? = r.toAdmin.getLast? := congrArg List.getLast? hc
  cases r with
  | values ws =>
    rcases List.eq_nil_or_concat ws with rfl | ⟨ws', w, rfl⟩
    · simp [invoke, Result.toAdmin, vals] at hl
    · rcases w with ⟨⟨t | t⟩, b⟩ | b | r <;> simp [invoke, Result.toAdmin, vals, Val.toAdmin] at hl
  | throw x => simp [invoke, Result.toAdmin] at hl
  | trap => simp [invoke, Result.toAdmin] at hl

/-- An entering thread is at no callout. -/
theorem entry_no_callout {Lh : List Val} {s : Store Nat} {t : Thread}
    (he : EntryO I G R fs ia iu Lh s t) {h : Nat} {args : List Val} :
    ¬ CalloutAt s t h args := by
  obtain ⟨a, v, fi, code, ps, rs, rfl, -, -, -, -, hf, hcode, -⟩ := he
  rintro ⟨E, b, hd⟩
  have hn : decompose? s (vals [v] ++ [.ref (.func a), .callRefType
      ((s.funcs[a]?.map FuncInst.type).getD default)]) = none :=
    Silmaril.Wasm.Logic.Hoare.decompose?_call_wasm trivial hf hcode
  have hc : (Thread.pending a [v]).config s = invoke s a [v] := rfl
  rw [hc] at hd
  simp only [invoke] at hd
  rw [hn] at hd
  cases hd

/-- **The step of an entering thread** enters the callee frame, which is invariant. -/
theorem entry_step {P : Profile} {Lh : List Val} {s s' : Store Nat} {t t' : Thread}
    (he : EntryO I G R fs ia iu Lh s t) (hst : InternalP P (s, t) (s', t')) :
    InvO I G fs ia iu Lh (t'.config s') ∧ s' = s := by
  obtain ⟨a, v, fi, code, ps, rs, rfl, -, hv, hs, hr, hf, hcode, hexp, hn, hm, hpl, hok⟩ := he
  obtain ⟨f', code', rfl, hstep⟩ := hst
  have hinv : (Thread.pending a [v]).config s =
      ⟨s, {}, vals [] ++ vals [v] ++ [.ref (.func a), .callRefType fi.type]⟩ := by
    simp [Thread.config, invoke, hf, vals]
  rw [hinv] at hstep
  have hc := Silmaril.Wasm.Logic.Hoare.call_step_inv (c := .callRefType fi.type) trivial hf hcode hexp
    hn hstep
  simp only [vals, List.map_nil, List.nil_append, Config.mk.injEq] at hc
  obtain ⟨rfl, rfl, rfl⟩ := hc
  exact ⟨invC_entry hs hv hr hm hpl hok, rfl⟩

end

end Silmaril.Wasm.Resource.OBClient
